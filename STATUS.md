# Project Status (current)

Updated: 2026-09-24

**Part A G2v + G2w-a + G2w-b, the countdown drains on the parsed target, under a semantic linear
cap, at a fixed cubic budget (infrastructure only).**
Two new pnp4 modules, `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownIterationBridge`
and `Pnp4.Frontier.ContractExpansion.ContentCountdownLinearCap`. There is **no new machine, no new
state, no new table row and no new pnp3 module**: every step is G2s-a's fixed 11-state, 33-row table,
run for longer by G2u. Write `N = a+m` and `d = borrow x w zeros`. Ten public theorems: the G2v
surface includes room equivalences and one-way execution results; G2w adds one-way semantic and
execution results plus one plain equation between two spellings of a split word.

G2v is to G2u exactly what G2t was to G2s-a: the *value*. G2u's `register_drained` is stated for a
universally quantified `v` and supplies none — its own probes use the hand-picked literals `24` and
`3` — and on a decoded header the G2r bridge already proves both digit facts for the decoded target
`n`, so `v := n` is the whole content of the slice.

* `countdown_width_eq_gammaZeros` (two hypotheses, a decoded header and a decoded width): the
  **physical** width `FixedContentGammaTerminator.gammaZeros?` reads off the word equals the
  **canonical** `gammaZeros n = bitLength (n+1) - 1` the pnp4 layout computes from the decoded
  target, and the adjacent-power bounds hold at that common value. The proof is exponent uniqueness
  on `2^zeros <= n+1 < 2^(zeros+1)`; both widths are already functions of data, so this is an
  equation between two computed quantities and **not** extraction of a value from a proof.
* `countdown_drain_cap_iff_machine_room` (the same two): the explicit lane cap `n <= F` together
  with `gammaZeros n + 2 + F <= a+B` is G2u's `lane_room` premise once the width is recovered — the
  same condition as the physical `zeros+2+F <= a+B` and as the tape form
  `a+m+3+zeros+F < tapeLength (pairLength a m) B` — and cap plus room **imply** G2t's first-round
  room `2*(n+1) < 2^(a+B)`. The converse is **not** stated and is false in general;
  `probe_countdown_drain_room_strictly_stronger` exhibits a literal split where G2t's room holds and
  this one fails at *every* `F` the cap admits.
* `countdown_drained_header_value` (five: matching tag, decoded header, `3 <= n`, the cap, the
  room): out of the landed `startConfig` the machine *enters* `qLoop` on the separator blank
  `N+2+zeros` after exactly `d+2` steps with the register holding `n` cell by cell, and after
  exactly `fullClock zeros d n` steps is in the absorbing `qDone` there with tape
  `loopTape B x w zeros 0 n` — every register cell `some false`, exactly `n` marks filling
  `[N+3+zeros, N+3+zeros+n)`, blanks from `N+3+zeros+n` on — and that endpoint persists. `3 <= n`
  reaches `2 <= zeros`; G2u's drain needs no positivity, so unlike G2t nothing here uses `1 <= n`.
* `countdown_drained_parsed_target` (five, with the header replaced by a successful
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec, no monotonicity and no
  injectivity premise): `pr.2.n = pr.1`, the decoded header and width, and the same endpoint at the
  actual parsed target.

G2w-a supplies a *value* for `F`, as semantics rather than as parsing. No theorem bounds the target
from parser success alone, and none is claimed: the source is virtually zero-padded, so the strict
parser's returned target is tied to no bound on the physical length. Content *acceptance* does bound
it, at the concrete `treeCircuitWitnessCodec (thresholdPoly k)`.

* `contentSemanticAccepts_parsed_target_le_length` (two: the successful parse and the Boolean
  acceptance; the exponent `k` is data): `pr.2.n <= N` for `z : PrefixBitVec N`. Two branches. If
  `treeMCSPPrefixM codec pr.2.n <= N`, the layout bound `instanceSize_lt_treeMCSPPrefixM` already
  places `pr.2.n` below it. Otherwise FEAS-0's
  `contentAccepts_parsed_tableLen_le_of_header_target_wide` turns acceptance into
  `tableLen pr.2.n = 2^pr.2.n <= N`, and `pr.2.n < 2^pr.2.n` finishes;
  `contentInput?_target_eq_contentHeader` is what lets the wide case be read at the parsed target
  rather than the header's. Neither branch needs `0 < N`.
* `contentSemanticAccepts_eq_false_of_length_lt_parsed_target` is the contrapositive in the form a
  routing phase would consume: a successful parse with `N < pr.2.n` makes the frozen Boolean checker
  **reject**. It is a statement about `contentSemanticAccepts` and about nothing else.
* `contentSemanticAccepts_parsed_target_le_pair_length` is the same bound at the split
  `z := Fin.append x w`, where `N` is the compacted content length `a+m` the fixed-phase tape ABI is
  laid out against.
* `countdown_drained_accepted_content` takes it: on an accepted word whose parse succeeds, G2v's
  drain runs at `F := a+m`, so the lane cap is **derived** from acceptance instead of assumed. The
  room stays a hypothesis.

G2w-b closes the remaining free budget by *choosing* it, at
`B := polyClock 3 (pairLength a m) = (2*a+1+m)^3 + 3`, a fixed cubic function of the split's own two
lengths. Acceptance caps the target at `N`, `gammaZeros n <= n` caps the width at `N`,
`borrow_pins` caps the borrow by the width, and G2u's clock expands to
`fullClock zeros d n = d + n*n + n*(2*zeros+6) + 2*zeros + 7`, whose every summand is then below a
fixed quadratic in `N`; the cube dominates it because `3 <= pr.2.n <= N` is in force.

* `concatBitstring_eq_append` is a word-shape bridge and nothing else: the verifier interface's
  `concatBitstring x w` and the fixed-phase split `Fin.append x w` are the same function of the two
  blocks. No parse, no acceptance, no header, no codec and no machine occurs in it.
* `countdown_drained_accepted_content_at_polyClock` has exactly **three** proposition hypotheses —
  the successful parse, the Boolean acceptance and `3 <= pr.2.n` — and no others: no tag premise
  (the factorization `fixedTag_semantic_factorization` derives it from acceptance), no cap, no
  room, no free `B`, no free `F`, no runtime premise and no correctness premise. Both the room
  `gammaZeros pr.2.n + 2 + N <= a+B` and the clock bound `fullClock zeros d pr.2.n <= B` are
  **conclusions**, exported as conjuncts alongside `3 <= N` and the derived tag, and the endpoint is
  transported from `fullClock` to exactly `B` steps by the persistence conjunct G2v already proves.
* `probe_countdown_polyClock_accepted_target_three` inhabits those three premises **jointly** — one
  accepted word per exponent, GATE-0's zero-prefix query for the all-false table on three variables
  followed by its certificate — at the pinned target `pr.2.n = 3` and hence the pinned width
  `gammaZeros 3 = 2`, and reads the `qDone` endpoint state back after exactly `B` steps. So G2w-b
  is not a statement about an empty premise set. That probe exhibits one word per exponent and
  claims nothing about any other; in particular it exhibits no *rejected* and no *overshooting*
  word.

Deferred and deliberately not claimed. The **fence**: `F` is a parameter of every G2v statement, the
tape is the unchanged canonical `loopTape` — blank at `N+3+zeros+F` — and nothing here lays a cutoff
cell, adds a `qOverflow` state or shows that any execution theorem survives an installed
`some false` in the lane. The executed-fence requirement recorded in the G2s-a and G2u entries below
stands unchanged: the lane is still uncapped *in the machine*, a target too large for the budget
still runs `qRunEnd` off the end of the tape and sticks there, which is a timeout and therefore
neither verdict, and G2w-a's bound does not change that — it identifies a cap value that is
legitimate for accepted words, not a mechanism that enforces one. The *other* half of that recorded
requirement, that the `F = N` justification be derived or replaced, is what G2w-a supplies, and only
in the form stated above: `F = N = a+m` for **accepted** words, at the concrete
`treeCircuitWitnessCodec (thresholdPoly k)` and conditional on acceptance, never from parser success
and never codec-generically. The executed-fence half stands. The **room** is carried and never
derived in G2v and G2w-a — `B` is a free budget there — and is sufficient and used, never shown
necessary; G2u's `check_below_room_drain_probe` still exhibits a budget where it fails while the
drain completes. G2w-b **derives** that room, but only by instantiating `B`: the condition is still
sufficient only, and nothing shows the cubic budget necessary. The **exponent** `3` is chosen to
dominate the quadratic clock; nothing shows it least and no smaller exponent is ruled out. The same
number `B` plays two roles in the G2w-b statement — the tape budget `startConfig` and `tapeLength`
are laid out against, and the number of steps the machine is run for — and that is an instantiation
choice, not a theorem: nothing says the two must agree, only that this one value is large enough for
both. `polyClock` is the repository's pinned clock family, and using it here is **not** a runtime,
`DecidesWithin`, `UniformP` or `NP` claim about anything.
**First arrival**: `qDone` absorbs, so the all-times conjunct is persistence and nothing more, and no
theorem says `qDone` is entered for the first time at `fullClock zeros d n`. **Every converse**:
nothing derives a header, a width, `2 <= zeros`, the cap, the room, the borrow length or a parsed
target from `qDone`, from the endpoint tape or from a mark in the lane, and no endpoint-to-parse
direction exists; on the G2w-a side nothing derives acceptance, a parse or a header from
`pr.2.n <= N`, and a `false` verdict can equally come from a failed parse or a failed witness check.
The more expensive `boundedContentCap` alternative — a polynomial lane derived from
`boundedContentInput?` success rather than a linear one derived from acceptance — is documented in
the G2w-a module and **not implemented**, and **no new direct import** is taken for it.
`BoundedContentSemanticVerifier` and the I1 gate-closure module are both already in the transitive
closure of both new modules, through `FixedContentTagGateCorrect`, which the G2v bridge reaches via
the G2o header-value bridge; the accurate statement is that no declaration of `boundedContentInput?`
or of its verifier is *used* here. What the new proofs do use from that direction is G2o's
`contentInput?_target_eq_contentHeader`, whose own proof invokes I1's
`contentInput?_lengthGate_vacuous`; on the G2w-a side the used dependencies are FEAS-0's
`contentAccepts_parsed_tableLen_le_of_header_target_wide` and `instanceSize_lt_treeMCSPPrefixM`. The
degenerate widths `zeros <= 1` stay out of reach of the machine theorems, since `3 <= n` forces
`2 <= zeros`; the two G2v parser-side theorems carry no width premise and cover them. The gamma
leading-digit convention stays destroyed and the endpoint register is all `some false`. Also every
malformed-gamma branch, parser execution, `accepts`, `AcceptsAt`, language membership, advice
freedom, `NP` membership, `ContentVerifierBridge` and P-vs-NP mainline progress. The lane holds `n`
**marks** — the tally is exactly as long as the decoded target, stated as a cell predicate, not as a
claim that the machine re-encoded `n` in unary. `fullClock` counts this phase's steps alone, not one
of the steps `startConfig` embeds and no clock of any earlier phase, so nothing here composes a
pipeline clock. `qDone` is phase-local acceptance of a machine handed a retagged actual prior
endpoint, not raw-input language acceptance. Infrastructure only.

**Part A G2u, the countdown iterates and drains the register (infrastructure only).**
New pnp3 module `Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration`, the iteration the
G2s-a entry below deferred as G2s-c. There is **no new machine and no new table row**: every step is
G2s-a's fixed 11-state, 33-row table, run for longer. Write `N = a+m` and `S = N+2+zeros` for the
separator blank. Three clocks and three public execution theorems, all composing landed ones.

* `roundsClock zeros r k = k*k + k*(2*zeros+2*r+6)` is the closed form of
  `sum_{i<k} roundClock zeros (r+i)`, written so that no `Nat` subtraction occurs anywhere;
  `drainClock` adds the exhaustion and `fullClock` the entry. `rounds_clock_pins` pins the three
  closed forms, the recurrence `roundsClock zeros r (k+1) = roundClock zeros r +
  roundsClock zeros (r+1) k` that drives the induction, and
  `fullClock zeros d 1 = firstClock zeros d + zeroClock zeros`, which says exactly that the
  one-round case is G2s-a's `first_round` followed by G2s-a's exhaustion. `high_iff_lt` is the only
  new arithmetic: no digit above `zeros` and `v < 2^(zeros+1)` are one condition.
* `iterate_generic` (seven hypotheses: the room, `r+k <= F`, `k <= v`, the width hypothesis and the
  three configuration equations): `k` rounds out of an arbitrary `qLoop` configuration on `S` cost
  exactly `roundsClock zeros r k` and leave `qLoop` on `S` with the register holding `v-k` and
  `r+k` marks — the same canonical `loopTape`, so the endpoint is again an entry point of the same
  theorem. `k <= v` and the width hypothesis are both load-bearing: drop either and some round meets
  a register whose `zeros+1` cells are all `false`, which by G2s-a's own `exhaust_generic` runs to
  the absorbing `qDone` instead of borrowing, so at `0 < k` the conclusion fails in state and in
  tape. Both failures land on the same separator cell, so neither is a head mismatch.
* `drain_generic` (six: `r+v <= F` replaces both `r+k <= F` and `k <= v`): taking `k := v` empties
  the register and G2s-a's `exhaust_generic` then fires, so after exactly
  `drainClock zeros r v` steps the machine is in the
  absorbing `qDone` on `S` with an all-`false` register and `r+v` marks, and that endpoint persists.
  There is no `1 <= v` hypothesis — at `v = 0` no round runs and the exhaustion fires at once.
* `register_drained` (seven): the concrete exact run, not out of an arbitrary configuration but out
  of the landed phase-local `startConfig B x w` — the *actual* G2q machine retagged at G2q's own
  length-only `deadline (a+m)`. It re-derives G2s-a's `first_round` entry identification, the
  portion that does not use positivity, and composes `entry_generic` with `drain_generic` at
  `r = 0`: the machine *enters* `qLoop` on `S` after exactly `d+2` steps with the register holding
  `v`, and after exactly `fullClock zeros d v` steps is in `qDone` there with every register cell
  `some false`, exactly `v` marks in `[N+3+zeros, N+3+zeros+v)`, blanks beyond, and the endpoint
  persisting. Its hypotheses are `first_round`'s with `1 <= v` dropped and the room split into
  `v <= F` and `zeros+2+F <= a+B`. `v = 0` is a legitimate `drain_generic` case but cannot inhabit
  these digit hypotheses under `2 <= zeros`, so no concrete zero-target coverage is claimed.

**The fence policy, reconciled.** The G2s-a entry recorded two requirements: that the iteration's
loop theorem take `F` as a parameter with room premise `zeros+2+F <= a+B`, and that the `F = N`
justification be derived or replaced first. They are about two different objects. This slice
satisfies the first literally and leaves the second untouched. Its theorems are **canonical bounded
execution lemmas**: `F` is a parameter of the *statement*, the tape is the unchanged canonical
`loopTape`, and no cell of it is a cutoff. They are **not** execution with an installed cutoff and
are not claimed to survive one — an installed `some false` at `N+3+zeros+F` is not a `loopTape`,
which is blank there, so the execution theorems would have to be re-proved against that tape and nothing
here is evidence that it can be. The executed-fence requirement stands unchanged and undischarged
for the fenced machine a later phase must build. The production statements leave `F` abstract; the
tests use literal budgets. No general `F = N` bound is claimed *here*.

The `F = N` half of that obligation has since been supplied separately, by G2w-a in the entry
above, which changed no declaration of this slice: `contentSemanticAccepts_parsed_target_le_pair_length`
derives `pr.2.n <= a+m` for **accepted** words at the concrete
`treeCircuitWitnessCodec (thresholdPoly k)`, covering both the wide and the narrow case. It remains
codec-specific and conditional on acceptance — parser success alone still bounds no target — and it
installs nothing, so the executed-fence half of the requirement stands undischarged.

`lane_room` is **sufficient and used, never shown necessary**, and it is not even the tightest
sufficient condition: it reserves exactly the cell an installed cutoff would occupy, so it can fail
where the canonical unfenced drain still completes. `check_below_room_drain_probe` exhibits one — at
`a = m = zeros = 0`, `v = F = 1`, `B = 2` the condition reads `3 <= 2` and fails, while
`drainClock 0 0 1 = 12` steps still reach `qDone` with the register cleared and one mark laid.

Deferred and deliberately not claimed. The **fence phase** itself: the lane is still uncapped in the
machine, a register too large for the budget still runs `qRunEnd` off the end of the tape and sticks
there, which is a timeout and therefore neither verdict, and the `qRunEnd`-on-`some false` row stays
pinned and unexercised. The **pnp4 parsed-target drain**, and with it every connection to
`contentHeader?`, `contentInput?` or a parsed target: `v` is universally quantified here, the
probes' `24` and `3` are hand-written literals, and no theorem of pnp3 produces either from a parse
— that companion has since landed separately, as the G2v entry above, which changed no declaration
of this slice. Also every converse, first arrival — `qDone` absorbs, so every persistence conjunct is persistence
and nothing more — any footprint or budget theorem, a malformed-gamma branch, parser execution,
`accepts`, `AcceptsAt`, `ContentAccepts`, language membership, `ContentVerifierBridge` and P-vs-NP
mainline progress. The gamma leading-digit convention stays destroyed. The lane holds `v` **marks**,
where `v` is the parameter whose register digits are *hypothesised*; calling them the target in
unary would be a claim about a decoded value and nothing here decodes anything. `qDone` is
phase-local acceptance of a machine handed a retagged actual prior endpoint, not raw-input language
acceptance, and every clock counts this phase's steps alone — not one of the steps `startConfig`
embeds. Infrastructure only.

**Part A G2t, the first countdown round runs on the parsed target (infrastructure only).**
New pnp4 module `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownBridge`, the
companion the G2s-a entry below deferred. There is **no new machine and no new pnp3 module**: the
run is G2s-a's `first_round`, unchanged. G2s-a states it for a `v` that is universally quantified
and supplies none — its own probes use the hand-picked literals `24` and `23` — and on a decoded
header the G2r bridge already proves both digit facts for the decoded target `n`, so `v := n` is
the whole content of this slice. Write `N = a+m` and `d = borrow x w zeros`. Three public theorems,
all one-way out of a decoded `contentHeader? = some …` or out of a successful dependent parse.

* `countdown_room_iff_target_bound` (two hypotheses, a decoded header and a decoded width): on that
  header the three forms `2*(n+1) < 2^(a+B)`, `zeros+2 <= a+B` and
  `a+m+3+zeros < tapeLength (pairLength a m) B` are the same condition, the doubling being exact
  because the gamma bounds put `2*(n+1)` in `[2^(zeros+1), 2^(zeros+2))`. Two
  further conjuncts place it against G2q's room: it implies it, and at the boundary width
  `zeros+1 = a+B` G2q's holds while this one fails. Unlike the G2r analogue both halves of that
  separation are proved rather than probed, and `probe_countdown_room_boundary_nonvacuous` only
  shows the boundary hypothesis is inhabited.
* `first_countdown_header_value` (four: matching tag, decoded header, `3 <= n`, and the room
  `2*(n+1) < 2^(a+B)`): the landed `startConfig` *enters* `qLoop` on the separator blank `N+2+zeros`
  after exactly `d+2` steps with the register holding `n`, and after exactly
  `firstClock zeros d = 2*zeros+d+9` steps is back in `qLoop` there with the register holding `n-1`
  and **one mark** at `N+3+zeros`. Six cell conjuncts read every index of the endpoint tape, and the
  endpoint register cells pin `n-1` among the values with no bit above `zeros`. `3 <= n` does two
  jobs: it reaches `2 <= zeros` and discharges G2s-a's `1 <= v`.
* `first_countdown_parsed_target` (four, with the header replaced by a successful
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec, no monotonicity and no
  injectivity premise): `pr.2.n = pr.1`, the decoded header and width, and the same concrete
  endpoint at the actual parsed target `pr.2.n`.

A fourth number is now on the tape. `zeros` is the physical gamma width, `n+1` the encoded gamma
integer, `consumed = 2*zeros+1` and `treeMCSPPrefixM codec pr.1` length conventions, `n` what G2r
left in the register, and `n-1` what this round leaves there. The lane holds one **mark**; calling a
tally the target in unary would be a claim about a decoded value and no theorem here decodes
anything.

Deferred and deliberately not claimed. The **iteration**: this bridge is one round and one only —
nothing *here* composes rounds or states a clock beyond `firstClock zeros d`, which counts this
phase's steps alone, and the pnp3 iteration landed later as G2u above is not carried across to a
parsed target by anything in this bridge — the G2v entry above is the bridge that does it, and it
changed no declaration of this one. **Persistence**: `qLoop` is not terminal, so unlike G2r's
`qDone` these endpoints hold at
exactly their stated time and there is no all-times conjunct, no deadline and no clamp. The
**fence**: the room allocates the *first* lane cell and is not a bound on the countdown; a target
too large for the budget would run the lane off the tape, which is a timeout and therefore neither
verdict, and nothing here excludes that. Also every converse, first arrival, any footprint or budget
theorem, any malformed-gamma branch, the exhaustion, parser execution, `accepts`, `AcceptsAt`,
`ContentAccepts`, language membership, `ContentVerifierBridge` and P-vs-NP mainline progress. The
gamma leading-digit convention stays destroyed. Infrastructure only.

**Part A G2s-a, the gamma target unary countdown round (infrastructure only).**
New pnp3 module `Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown`: a **new** fixed 11-state,
33-row machine, the second new table since the G2p-d round. Write `N = a+m`. Out of the retagged
G2q endpoint it *enters* `qLoop` on the separator blank `N+2+zeros` in exactly `d+2` steps, writing
nothing; one round then subtracts one more from the target register and lays **one mark** in the
tally lane past that blank, in exactly `roundClock zeros r = 2*zeros+2*r+7` steps at `r` marks
already laid; an all-`false` register exhausts to the absorbing `qDone` in exactly
`zeroClock zeros = 2*zeros+5` steps with the tape unchanged. `first_round` runs the entry and the
first round out of the phase-local `startConfig` at `firstClock zeros d = 2*zeros+d+9`.

Everything is symbol-driven: no width, digit index, register address, mark count, clock, counter,
proof term, advice or producer mark occurs in any row, and every branch is decided by the one symbol
under the head. `qPadL` and `qPadR` pad each sweep back out to the full register, which is why the
round clock does not depend on how long the borrow ran. The statement-level `lowRun` is read off the
value and is private and structural; the machine finds the same cell by reading symbols.

**Entry ABI**, which any phase inserted before this machine must re-establish: `qStart` on the
cleared stopping digit `some false` at `N+1+zeros-d`, exactly `d` cells of `some true` to its right,
the separator blank at `N+2+zeros`, a blank lane beyond.

Deferred and deliberately not claimed. The **iteration** (G2s-c): nothing *in this pnp3 module*
iterates the round — that has since landed separately, as the G2u entry above, under an explicit
lane-budget parameter `F` and installing no cutoff. The **fence**: the
lane is uncapped, so a register too large for the budget runs `qRunEnd` off the end of the tape and
sticks there, which is a timeout and therefore neither verdict; the `qRunEnd`-on-`some false` row is
the reject hook the future fence phase will use, and it is pinned and unexercised. The **pnp4
bridge**, and with it every connection to `contentHeader?`, `contentInput?` or a parsed
target: `v` is universally quantified and no theorem *in this pnp3 module* supplies one — that
companion has since landed separately, as the G2t entry above. A footprint or budget
theorem, so every room premise is sufficient and used but never shown necessary. Every converse. A
malformed-gamma branch, since G2q characterises no non-`qDone` endpoint to route. And any
restoration of the gamma leading-digit convention, which this phase destroys further each round.

`qLoop` does not absorb, so every `qLoop` endpoint is an exact time and **not** a deadline, and
`exhaust_generic`'s all-times conjunct is persistence, not first arrival — no theorem says `qDone`
is entered for the first time at `zeroClock zeros`. The lane holds marks; calling it the target in
unary would be a claim about a decoded value, and nothing here decodes anything. `qDone` is an
internal control tag of a machine started from a phase-local retag of an actual prior run, so
reaching it is neither halting of a composed machine nor language acceptance; the module states no
`accepts`, no `AcceptsAt` and no language membership, and the clocks compose no earlier clock.
Infrastructure, not P-vs-NP mainline progress.

**Part A G2r, the decremented register is the parsed target's digits (infrastructure only).**
New pnp4 module `Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetRegisterDecrementBridge`,
the composition that both entries below deferred. There is **no new machine and no new pnp3
module**: the run is G2q's `register_decremented`, unchanged, and everything added is a statement
about what its endpoint cells *are*. Write `N = a+m` and `d = borrow x w zeros`. Five public
theorems, all one-way out of a decoded `contentHeader? = some …` or out of a successful parse; no
converse is stated anywhere.

The composition is short, and that is the point. G2q's `decBit_sub_one` is arithmetic about an
**arbitrary** `v` whose bit `zeros-j` is register digit `j` at every `j ≤ zeros` and which has no
bit above `zeros`; G2p-g's `exhaustion_register_digits` proves exactly those two facts for
`v = n+1` on a decoded header. Instantiating one at the other, and using `n+1-1 = n`, is the
whole mathematical content of this slice: the register that held the digits of the encoded gamma
integer `n+1` now holds the digits of the **decoded target `n` itself**, at every `j ≤ zeros`.

Three theorems are parser-side: no machine, no tag and no clock occurs in any of them, and only
`decrement_room_iff_target_bound` mentions the budget `B`. `decremented_register_digits` (one
propositional hypothesis, a decoded header) produces `zeros` with `consumed = 2*zeros+1`, the
bounds `2^zeros ≤ n+1 < 2^(zeros+1)`, the bound `d ≤ zeros` that keeps the borrow inside the
register, the equation `decBit x w zeros d j = n.testBit (zeros-j)` at every `j ≤ zeros`, and the
completeness fact that `n` has no bit above `zeros`, so those `zeros+1` cells carry *all* of the
decoded target's digits. `decBit` and `borrow` are G2q's endpoint-content functions — pure
functions of the word and the width — so this theorem runs nothing.
`decremented_register_determines_target` (four hypotheses) adds uniqueness: any `v` whose bit
`zeros-j` is the decremented digit `j` for every `j ≤ zeros` and which has no bit above `zeros`
**is** `n`. It is arithmetic about digits, not a decoding step any machine performs.
`decrement_room_iff_target_bound` (two hypotheses) makes G2q's **stronger** room premise legible:
`n+1 < 2^(a+B)`, `zeros+1 ≤ a+B` and `N+2+zeros < tapeLength (pairLength a m) B` are the same
condition; it implies G2p-g's `n+1 < 2^(a+B+1)`; and at the boundary width `zeros = a+B` it
*fails*. That G2p-g's can still hold at that boundary is no conjunct of it — the probe
`probe_decrement_room_strictly_stronger` exhibits that at a literal word, and only together do
the two show the one extra cell `qRegEnd` needs is a real strengthening rather than a
restatement.

Two are machine-side, at G2q's own endpoint. `decremented_register_header_value` (four
hypotheses: matching tag, decoded header, `3 ≤ n`, and the room `n+1 < 2^(a+B)`): the landed G2q
machine run out of the landed `startConfig` for exactly `decClock N zeros d` steps is in `qDone`
on the stopping cell `N+1+zeros-d` with tape `decTape B x w zeros d`, every register cell `N+1+j`,
`j ≤ zeros`, holds `some (n.testBit (zeros-j))`, `n` has no bit above `zeros`, those endpoint
cells *pin* `n` among all values with no bit above `zeros`, every cell outside the register is the
incoming G2p-f endpoint cell of `finishTape B x w zeros`, and the endpoint persists at every later
time. One conjunct looks backwards instead of forwards — the incoming `finishTape` register cells
hold `some ((n+1).testBit (zeros-j))` — so both sides of the subtraction are visible in a single
statement. `decremented_register_parsed_target` (four hypotheses, for an arbitrary codec) replaces
the header by a successful **dependent parse** `contentInput? codec (Fin.append x w) = some pr`,
exports `pr.2.n = pr.1` — the target the parsed `PrefixInput` carries, which is what
`ContentAccepts` feeds to the search relation, is the outer Sigma index and the target a decoded
`contentHeader?` *returns* — and restates every endpoint conjunct in terms of `pr.2.n`. That is
the actual parsed dependent target, not a convention length: `consumed = 2*zeros+1` and the window
length `treeMCSPPrefixM codec pr.1` stay length conventions, and no conclusion here puts either in
a register cell.

**The gamma leading-digit convention is not restored, and must not be read back in.** The
convention encodes `n` as the bits of `n+1` precisely so that the leading digit is a `true` the
decoder can find, and subtracting one destroys that. When the incoming register is exactly
`2^zeros` the borrow runs its whole length and clears digit `0`, so the decremented register's top
cell is `some false`; the theorems say so rather than excluding it, and the probe
`probe_decrement_cleared_top_digit` exhibits the case on a literal word — gamma `0001`, payload
`000`, header `(7, 7)`, `borrow = 3`, `decClock 15 3 3 = 18`, endpoint register `0111₂` at cells
`16 … 19`, the four digits of `7` with a `false` on top. For the same reason G2p-g's virtual-tail
conjunct has **no analogue** here: a truncated payload's register cell is `some false` before the
phase and the borrow may flip it to `some true`, so only the general statement, that the cell holds
`n`'s digit, is made. The other probe, `probe_decrement_register_width_three`, is the ordinary
shape: header `(12, 7)`, incoming register `1101₂`, `borrow = 0`, `decClock 15 3 0 = 15`, endpoint
register `1100₂` — the digits of `12`. Both derive their cells from
`decremented_register_header_value` for every budget and reduce no `startConfig`.

Deferred, and deliberately not claimed: every converse — nothing derives a header, a width,
`2 ≤ zeros`, room, or the borrow length from `qDone`, from the endpoint tape, or from a digit at a
register cell; parser execution of any kind (`n` and `pr` occur only in statements, and G2q's
control reads one tape symbol and nothing else); reading the register as a number *on the tape*,
the pinning conjunct being arithmetic about the digits found there; a footprint or budget theorem,
so the room premise is carried and sufficient, never shown necessary; a malformed-gamma branch and
the degenerate widths `zeros ≤ 1` **on the machine side**, which `register_decremented` inherits
from `payload_exhausted` and excludes, while the three parser-side theorems carry no width premise
and cover them; **first arrival**, which no conjunct of either machine theorem states — they give
the endpoint at exactly `decClock` and its persistence at every later time, and nothing says
`qDone` is not entered earlier, minimality being G2q's own `decrement_strict`, stated there for an
arbitrary configuration of the G2p-f endpoint shape and neither instantiated nor restated here;
and the handoff of this endpoint onward.
Given a decoded header `3 ≤ n` is exactly `2 ≤ zeros` — both directions follow from the exported
bounds, only the direction used here is proved. `decClock` counts the steps of the G2q phase
alone, not one of the steps its `startConfig` embeds, so no clock here composes a pipeline, and
`qDone` is an internal control tag of a phase whose `startConfig` retags an *actual* prior run, so
reaching it is neither halting of a composed machine nor language acceptance. Nothing here is a
`ContentAccepts` statement. Clock composition, the fixed parser, advice freedom, `NP` membership,
`ContentVerifierBridge` and P-vs-NP mainline progress stay out of scope.

**Part A G2q, the gamma target register decrement (infrastructure only).** New pnp3 module
`Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement`, and the first **new machine** since
the G2p-d round: a fixed 7-state, 21-row table that subtracts one from the target register the
G2p-e/G2p-f loop left on the tape. A new table was unavoidable, not convenient — that loop only
ever appends a digit and marks a consumed gamma zero, and no row of its 22-state table performs a
borrow. Write `N = a+m`. Fifteen public theorems; every one of the module's 33 public declarations
is restated in the surface test and printed in `pnp3/Tests/AxiomsAudit.lean`.

Everything is symbol-driven, which is the design. No width, digit index, register address,
counter, proof term, advice or producer mark occurs in the table: every branch reads the one
symbol under the head. Out of G2p-f's endpoint — halted on the tag cell `7` with tape
`finishTape B x w zeros` — `qSeekTerm` runs right over everything that is not `some true`, so
the first it meets is the walking terminator (the restored gamma zeros are `some false`, the
consumed trail blank); `qSeekGap` runs right over the non-blank content, so the first blank it
meets is the boundary cell `N`; `qRegEnd` runs right over the register, so the first blank past it
is `N+2+zeros`, and one left step lands on the least significant digit `N+1+zeros`. `qBorrow` then
does the arithmetic in two rows: `some false` becomes `some true` and the head moves left,
`some true` becomes `some false` and the machine halts in the absorbing `qDone` there. The low run
of `false` digits is flipped, the `true` that stops it is cleared, every higher digit is left
alone — which is subtraction of one. `borrow_pins` produces the stopping index from G2p-d's
`registerBit_pins` and bounds it by `zeros`, so the sweep never leaves the register; `borrow` is a
statement-level quantity read off the digits, not advice, since no row of the table mentions it.

`decrement_generic` is that run out of an **arbitrary** configuration matching the G2p-f endpoint,
in exactly `decClock N zeros d = N+zeros+d-3` steps at borrow length `d`, ending in `qDone` on the
cell `N+1+zeros-d` with the whole tape equal to `decTape B x w zeros d`. The clock is **not**
length-only, and in two ways: it depends on the decoded width, and through `d` on the stored
digits. `clock_pins` decomposes it under the width guard `9+zeros ≤ N` and states the length-only
bound `deadline N = 3*N` in the guarded form `9+zeros ≤ N → d ≤ zeros → decClock ≤ deadline`;
both guards are hypotheses, not caution. `decrement_schedule` pins the control and head at every
time of the phase, so with `decrement_generic` the control is named at every time up to and
including the halt, and `qReject` is entered nowhere in that range — nor later, by the clamp.
`decrement_strict` proves both directions: `qDone` is not entered strictly earlier, and the
configuration is constant from `decClock` on, in particular at `deadline N`. That minimality is
measured from *this* configuration, not from the G2p-d `startConfig` of the previous phase.
`decTape_pins` says what the endpoint tape is: the register cells hold `decBit`, the stopping
cell is `some false`, the cells under it `some true`,
and every cell outside `[N+1, N+1+zeros]` is the incoming `finishTape` cell. It is a statement
about the tape function, not about which cells were visited.

`register_decremented` is the slice's concrete exact run, out of the phase-local `startConfig` on
four hypotheses: a matching tag, `gammaZeros? (Fin.append x w) = some zeros`, `2 ≤ zeros`
(inherited from G2p-f, so `zeros ≤ 1` stays outside the proved surface), and the room
`N+2+zeros < tapeLength (pairLength a m) B`. That room is one cell more than G2p-f's, because
`qRegEnd` finds the register's right end by the blank past it and by nothing else; `room_iff`
reads it as `zeros+1 ≤ a+B` and proves it implies G2p-f's own premise, so exactly one room
premise is carried. Sufficient and used, never shown necessary: there is still no footprint
theorem. The handoff consults no decoded data — `startConfig` retags the G2p-d round machine at
the **length-only** time `priorDeadline N = 3*(N*N)`, `handoff_exact` pins that retagging replaces
the control and nothing else, and `prior_covers` proves that time is at or past G2p-f's exact
`totalClock N zeros` at every decoded width, so G2p-f's clamp identifies the incoming
configuration. That is the length-only loop deadline the G2p-e/G2p-f loop never stated, and it
bounds that loop's own phase-local clock and nothing else: it counts no step the G2p-d
`startConfig` embeds, and `decClock` counts the steps of this phase alone.

What the decrement *means* is kept apart from what it *does*. `sub_one_bits` and `decBit_sub_one`
are arithmetic about `Nat` — no machine, no tape, no parser, no codec. For an **arbitrary**
natural `v` whose bit `zeros-j` is register digit `j` at every `j ≤ zeros` and which has no bit
above `zeros`, the endpoint digits are the bits of `v-1` at the same positions, and `v-1` has no
bit above `zeros` either. **No theorem here supplies such a `v`.** Those two hypotheses are
exactly what the G2p-g bridge's `exhaustion_register_digits` proves for `v = n+1` on a decoded
header, and composing the two is a pnp4 step this slice does not take; nothing here mentions
`contentHeader?`, `contentInput?`, or a parsed target. The G2p-g entry below says the register
holds the digits of `n+1` and not of `n`; this slice supplies the *machine* that borrows one out
of those cells, and not the identification of the result with `n`. That identification is now
supplied, outside this module, by the G2r bridge at the top of this file, which instantiates this
`v` at `n+1`; it changes nothing inside pnp3, which still mentions no header and no parse.

Nonvacuity is independent of the endpoint theorems. Two literal probes identify the phase-local
start configuration for every budget from G2p-f's `payload_exhausted` and `prior_covers` alone,
then reduce this machine's own `run` by kernel computation at `B = 0`. Both words decode to
`zeros = 4` behind the tag `10110010`, and they exercise the two shapes of the borrow. The
physical probe (`N = 17`, terminator at `16`, `totalClock 17 4 = 64`, `priorDeadline 17 = 867`)
has `borrow = 0` and `decClock 17 4 0 = 18`: `qBorrow` reaches the least significant digit `22` at
step seventeen, that digit is `some true`, and step eighteen is `qDone` on `22` with `[18,22]`
reading `11001` before and `11000` after. The truncated probe (`N = 15`, terminator at `14`,
`totalClock 15 4 = 54`, `priorDeadline 15 = 675`) has `borrow = 3` and `decClock 15 4 3 = 19`:
`qBorrow` walks `20, 19, 18` — three `false` digits, two of them the virtual zeros of the
truncated payload — and stops on `17`, so step nineteen is `qDone` on `17` with `[16,20]` reading
`11000` before and `10111` after. Those are cell contents read from the register's leading cell;
no probe claims them to be a decoded value. Both sample a cell outside the register and run past
the endpoint, exhibiting `qDone` absorbing. `check_probe_inputs_valid` and `check_clock_values`
pin the hypotheses and the literal clocks separately, and
`check_decBit_sub_one_instance` shows the arithmetic's premises are satisfiable — the truncated
register's digits are the bits of `24`, the endpoint's the bits of `23`. That `24` is a
**hand-written literal** matched to the digits; no theorem of this slice or of pnp3 derives it
from a parse, which is precisely the deferred pnp4 step.

Deferred by *this module*, and deliberately not claimed in it: that pnp4 bridge and every
connection to a parsed target — the bridge has since landed as the G2r entry at the top of this
file, and no declaration of this module changed;
a footprint or budget theorem; every converse — nothing derives `zeros`, the borrow length, or
anything about the incoming digits from `qDone` or from an endpoint cell; a malformed-gamma
branch; first arrival measured from the previous phase's `startConfig`; the handoff of this
endpoint onward; and **any restoration of the gamma leading-digit convention**. That last is a
real gap, not a formality: when the register holds exactly `2^zeros` the borrow clears digit `0`,
so the decremented register need not begin with a `true`, and nothing here re-establishes the
invariant the gamma encoding relies on. `qDone` is `machine.accept` of a machine started from a
phase-local retag of an actual prior run rather than from `initialConfig` on a raw pair input, so
reaching it is neither halting of a composed machine nor language acceptance; the module states no
`accepts`, no `AcceptsAt` and no language membership. Clock composition, the fixed parser, the
checks, advice freedom, `NP` membership and `ContentVerifierBridge` are out of scope. It is
infrastructure, not P-vs-NP mainline progress. Long-form design notes are in
`pnp3/Docs/UniformP_V1.md`.

**Part A G2p-g, the exhausted register is the parsed target's digits (infrastructure
only).** New pnp4 module
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetPayloadExhaustionBridge`, the
companion the G2p-f slice below left deferred. There is **no new machine and no new pnp3
module**: the run is G2p-f's `payload_exhausted`, unchanged, and everything added is a
statement about what its endpoint cells *are*. Write `N = a+m`. Five public theorems, all
one-way out of a decoded `contentHeader? = some …` or out of a successful parse; no
converse is stated anywhere.

Three are parser-side: no machine, no tag and no clock occurs in any of them, and only
`room_iff_target_bound` mentions the budget `B`, through the tape length.
`exhaustion_register_digits` (one propositional hypothesis, a decoded header
`contentHeader? (Fin.append x w) = some (n, consumed)`) produces the width `zeros` with
`consumed = 2*zeros+1`, `2^zeros ≤ n+1 < 2^(zeros+1)`, and the **register equation**
`registerBit x w zeros j = (n+1).testBit (zeros-j)` at *every* `j ≤ zeros` — the
bootstrap's leading `true` at `j = 0` is the header's own leading digit, and each later
`j` is the payload cell `8+zeros+j`. Two further conjuncts make "complete" precise. `n+1`
has **no** bit above `zeros`, so the `zeros+1` register cells carry all of its digits and
none is stored elsewhere. And for `1 ≤ j ≤ zeros` with `a+m ≤ 8+zeros+j` — the **virtual
tail**, where the payload cell has left the physical word — the register digit is `false`
*and* the parsed `(n+1).testBit (zeros-j)` is `false` too. That conjunct is the point of
the slice. `registerBit` pads with `false` because the cell is not in the word (on
`contentTape` it is blank); the decoder pads with a virtual zero because `contentHeader?`
reads through `VirtualZeroTailReader`. Those are two different paddings, and this is where
they are proved to agree, so a virtual `false` in a truncated register is *the parsed
target's own digit* rather than the default G2p-f could only call content.
`register_determines_target` (four hypotheses) adds uniqueness: any `v` whose bit
`zeros-j` is the register digit `j` for every `j ≤ zeros` and which has no bit above
`zeros` **is** `n+1`. Both premises are needed — without the second, `v + 2^(zeros+1)`
would match every cell. This is arithmetic about the digits, not a decoding step any
machine performs. `room_iff_target_bound` (two hypotheses) makes the room premise legible:
on a decoded header `n+1 < 2^(a+B+1)`, `zeros ≤ a+B`, and the premise G2p-f inherits from
the G2p-e iteration, `N+1+zeros < tapeLength (pairLength a m) B`, are the *same*
condition.

Two are machine-side, at G2p-f's own endpoint. `exhausted_register_header_value` (four
hypotheses: matching tag, decoded header, `3 ≤ n`, and the room `n+1 < 2^(a+B+1)`): the
landed G2p-d round machine run out of the landed `startConfig` for exactly
`totalClock N zeros` steps is in `qDone` on the tag cell `7` with tape
`finishTape B x w zeros`, every register cell `N+1+j`, `j ≤ zeros`, holds
`some ((n+1).testBit (zeros-j))`, every virtual-tail cell holds `some false` together with
the matching parsed `false`, those endpoint cells *pin* `n+1` among all values with no bit
above `zeros`, the tag cell `7` with the gamma zero field `[8, 7+zeros]` is back to the
incoming content tape, and the endpoint persists at every later time.
`exhausted_register_parsed_target` (four hypotheses, for an arbitrary codec) replaces the
header by a successful **dependent parse** `contentInput? codec (Fin.append x w) = some pr`
and exports `pr.2.n = pr.1` — the target the parsed `PrefixInput` carries, which is the
`pr.2.n` that `ContentAccepts` feeds to the search relation, is the outer Sigma index and
the target a decoded `contentHeader?` *returns* — then restates the register, pinning
conjunct included, in terms of `pr.2.n`. It re-exports every conjunct of the header form except the
gamma zero field restoration, which is about the tape and not about the target.

Three numbers stay apart. `pr.2.n` is the **actual parsed target**: the value a decoded
`contentHeader?`, and the dependent parser after it, *returns* once the gamma convention has
been applied — not a value the header stores. `n+1` is the **encoded gamma integer** that
convention writes: the integer whose bits physically occur in the header and in the
exhausted register, so that the leading digit is a `true` the decoder can find. The register
holds the digits of `n+1`, *not* of `n`, and the decrement is performed by no machine here
and is not claimed. `consumed = 2*zeros+1` is the header's
**cell count**, a length convention that is not the target and never sits in the register;
the parser's other length convention `treeMCSPPrefixM codec pr.1` occurs only in the type
of `pr`.

Room is carried, not derived. A decoded header does not imply it: `B` is free, and
`room_iff_target_bound` reads it as `zeros ≤ a+B`, a condition on the `x` side and the
budget. The surface probe `probe_exhausted_room_not_implied` makes that sharp — one
twelve-cell word with a matching tag and the decoded header `(5, 5)`, hence `3 ≤ n`, split
once as `a = 8, m = 4` and once as `a = 1, m = 11`, with the word identity of the two
splits pinned as a conjunct; every reader here sees `Fin.append x w`, so both splits decode
to the same header, but at `B = 0` room holds on the first and fails on the second. The
probe states the tape form on the first split and refutes the outer two of the three
equivalent forms on the second, which `room_iff_target_bound` makes all three. Room is
therefore sufficient and used,
never shown necessary: there is still no footprint theorem on the pnp3 side. Two further
probes derive their cells from `exhausted_register_header_value` for every budget: header
`(12, 7)` gives the wholly physical four-digit register `1101₂` at cells `16 … 19` with
`totalClock 15 3 = 31`, and header `(5, 5)` gives `110₂` at cells `13 … 15` whose last
digit is the virtual tail — endpoint cell `some false`, parsed `(5+1).testBit 0 = false` —
with `totalClock 12 2 = 5`, the finish alone.

The decrement of `n+1` to `n` is now discharged, in two steps that were landed separately. The
G2q machine above borrows one out of these very register cells and proves, arithmetically and for
an arbitrary `v`, that the resulting digits are the digits of `v-1`; the G2r bridge at the top of
this file instantiates that `v` with the `n+1` this entry's `exhaustion_register_digits` supplies,
so the decremented register is proved to hold the digits of `n` — at G2q's own endpoint, under its
stronger one-extra-cell room premise, and for the parsed `pr.2.n` as well. Nothing about *this*
entry's theorems changed: they are still about the G2p-f endpoint, where the register holds `n+1`.
Deferred, and deliberately not claimed here: that composition, which is G2r's; reading the
register as a number *on the tape* (the pinning conjunct is arithmetic about the digits found
there, not a decoding step the control performs — no machine here executes `contentHeader?`,
`contentInput?`, or any parser, and control reads a tape symbol and nothing else); every
converse — nothing derives a header, a width, `2 ≤ zeros`, or room from `qDone`, from the
endpoint tape, or from a digit at a register cell; a footprint or budget theorem; a
malformed-gamma branch; first arrival measured from `startConfig`. The two machine theorems
inherit G2p-f's exclusion of `zeros ≤ 1`, since on a decoded header `3 ≤ n` is exactly
`2 ≤ zeros` (both directions follow from the exported bounds; only the direction used here
is proved, as in G2p-c); the three parser-side theorems carry no width premise and do cover
those widths. `zeros = 2` is admitted, where the G2p-e round count `zeros-2` is zero and
the endpoint is the finish alone. `qDone` is an internal control tag of a phase whose
`startConfig` retags an *actual* prior run, so reaching it is neither halting of a composed
machine nor language acceptance, and `totalClock` counts no step that `startConfig` embeds,
so it clocks no composed pipeline. Nothing here is a `ContentAccepts` statement. Clock
composition, advice freedom, `NP` membership, `ContentVerifierBridge` and P-vs-NP mainline
progress stay out of scope.

**Part A G2p-f, the gamma payload exhaustion finish (infrastructure only).** New pnp3
module `Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion`. Still **no new
machine**: the landed G2p-d `FixedGammaTargetPayloadRound.machine` — the same fixed
22-state, 66-row table — already carries the stopping rule in its `qCntL`/`qFin` rows,
and `machine_reused` pins that identity together with the five rows this phase runs.
Write `N = a+m`.

What is new. G2p-e left the machine in the `r = zeros` instance of the loop invariant
`loopTape B x w zeros zeros`, where every gamma zero carries a consumed-source mark, so
`r = zeros` *is* exhaustion. Out of that configuration `exhaust_generic` proves the whole
finish: `qLoop` leaves the walking terminator into `qCntL`, `qCntL` scans left over the
blank trail, and the first non-blank it meets is cell `7+zeros` — at every earlier index
an unconsumed gamma zero, `some false`, which sent the round on through `qCntZ`, and here
a consumed mark, `some true`, which fires the `qCntL` row into `qFin`. `qFin` then sweeps
the counter field `[8, 7+zeros]` back to `some false` and halts on the tag cell `7`,
which a matching tag already holds as `some false`. The rule reads one tape cell and
nothing else: no width, digit index, address, counter value, proof term, advice or
producer mark occurs in control. Its hypotheses are a matching tag,
`gammaZeros? (Fin.append x w) = some zeros`, `1 ≤ zeros`, and the three projections of an
**arbitrary** incoming configuration — six propositional premises and **no room premise
at all**, because the finish only ever moves left from a head the hypothesis already
places inside the tape.

The restoration is the semantic point, and `finishTape_pins` states both halves of it.
On `[7, 8+zeros)` — the counter the loop consumed, plus the tag cell the sweep stops on —
the endpoint tape is back to the incoming `contentTape` and reads `some false`.
Everywhere else it is the incoming invariant untouched: consumed sources still blank, the
walking terminator still standing at `8+zeros+termWalk N zeros`, and the completed
register `[N+1, N+1+zeros]` still holding its `zeros+1` digits. So the endpoint is **not**
`contentTape`, and nothing claims it is; the probes pin a consumed payload cell blank and,
in the truncated shape, a content `false` overwritten by the terminator's `some true`.

Clocks. `exhaustClock N zeros = termWalk N zeros + zeros + 2`, where
`termWalk N zeros = walk N zeros zeros`: one step off the terminator, `termWalk N zeros`
blank-trail steps, the step that fires the rule, `zeros-1` further unmarking steps, and
the halt. It is neither length-only nor shape-independent — `2*zeros+2` on a physically
present payload, `N-7` on a truncated one — and it is the one clock of this loop that is
not padded flat, because the finish is performed once and no induction has to add up a
sequence of its costs. `clock_pins` pins both shapes and, under `9+zeros ≤ N`,
`exhaustClock N zeros ≤ roundClock N`; that guard is a hypothesis of the conjunct and not
editorial caution — at `N = 0`, `zeros = 100` the finish costs `102` while `roundClock 0`
truncates to `0`. `totalClock N zeros = loopClock N zeros + exhaustClock N zeros` counts the
G2p-e rounds and this finish only: not one step that `startConfig` embeds, so it clocks no
composed pipeline.

Because `qDone` absorbs — which `qLoop`, where both round endpoints sit, does not — this
endpoint may be transported forward, and `exhaust_strict` proves **both** directions
available here: the endpoint holds at every later time, and `qDone` is not entered at any strictly
earlier time, so `exhaustClock` is a proved first arrival. That minimality is measured
from the `r = zeros` configuration, not from `startConfig` — the G2p-e rounds carry no
strictness theorem, so `qDone`-freeness across them is established nowhere here — the two
probes pin a handful of pre-endpoint states only, not the absence of `qDone` throughout
that segment. `exhaust_schedule` pins the control at every time of the phase (`qLoop`,
then `qCntL`, then `qFin`), which with `exhaust_generic` leaves no time at which a source
or register state could occur. `payload_exhausted` is the slice's concrete exact run: on
a matching tag, a gamma field decoding to `zeros` with `2 ≤ zeros`, and the inherited G2p-e
room `N+1+zeros < tapeLength (pairLength a m) B` — four premises, the decode `gammaZeros?
(Fin.append x w) = some zeros` and the bound on `zeros` being two of them — the same machine
run out of the landed `startConfig` for exactly `totalClock N zeros` steps is in `qDone` on
cell `7`, its tape is `finishTape B x w zeros`, the gamma zero field is back to the content
tape, and the endpoint persists at every later time. The register conjunct is
**preservation, not completion**: that `[N+1, N+1+zeros]` holds its `zeros+1` digits is
G2p-e's `register_complete`, and all this slice adds is that the finish carries it through
unchanged — nothing decodes those digits, and where the payload is truncated the digits past
it are `registerBit`'s virtual `false`, which no theorem calls the payload's value. That
room premise is sufficient and used; it is not shown necessary, since there is no footprint
theorem.

Probes. Two literal probes identify the phase-local start configuration for every budget
from the landed G2p-d foundation endpoint alone, then reduce the round machine's own `run`
by kernel computation at `B = 0` across both remaining rounds *and* the finish, invoking no
execution theorem of this module. Both words decode to `zeros = 4`. The physical probe
(`N = 17`, `loopClock 17 4 = 54`, `termWalk 17 4 = 4`, `exhaustClock 17 4 = 10`,
`totalClock 17 4 = 64`) pins `qCntL` on the last counter mark `11` at step fifty-nine,
`qFin` on `10` at step sixty, `qFin` on `7` at step sixty-three, and `qDone` on `7` at step
sixty-four with cells `7,8,9,10,11` all back to `some false`, the consumed payload cell `13`
blank, the terminator at `16` and the register `[18,22] = true, true, false, false, true`.
The truncated probe (`N = 15`, `loopClock 15 4 = 46`, `termWalk 15 4 = 2`,
`exhaustClock 15 4 = 8`, `totalClock 15 4 = 54`) is two steps cheaper. That gap tracks `N`
alone: both probes lie in the band `9+zeros ≤ N ≤ 9+2*zeros`, where the clock is `N-7`, so
the pair is no witness of the clock's dependence on `zeros`. It pins the same restoration,
cell `14` carrying the terminator's `some true` over an input `false`, and the register
`[16,20] = true, true, false, false, false`. Both run past the endpoint, exhibiting `qDone`
absorbing. `check_probe_inputs_valid` states separately that both words satisfy the
tag/width hypotheses and, at `B = 0`, the room hypothesis.

Two of this slice's deferrals are now discharged by the G2p-g bridge above, which supplies
the pnp4 companion and ties every register cell — virtual tail included — to a digit of the
decoded header's, and of the actual parsed input's, target. A third is discharged on the
machine side by the G2q decrement above, which borrows one out of this endpoint's register in
a new fixed 7-state table, out of a phase-local retag of this slice's own endpoint; what that
slice does *not* supply is the identification of the result with `n`, so the digits-of-`n`
reading stays open. The rest stand as written. Deferred, and deliberately not claimed here:
that identification, any reading of the register as a *number* (`registerBit` gives content,
not a value), a footprint/budget theorem, every converse — nothing says that `qDone` at
`totalClock N zeros`, or any endpoint cell, implies anything about `zeros` — first arrival
measured from `startConfig`, the degenerate widths (`zeros = 0` is excluded from `exhaust_schedule`,
`exhaust_generic` and `exhaust_strict` by their `1 ≤ zeros` premise, which the tape-shape
theorem `finishTape_pins` does not carry; `zeros = 1` satisfies those three but is produced
by nothing here, since `payload_exhausted` needs `2 ≤ zeros`; `zeros = 2` is covered, with
`loopClock N 2 = 0` making `payload_exhausted` the finish applied directly to the retagged
foundation endpoint), and a malformed-gamma branch. `qDone` is `machine.accept` of a
machine started here from a phase-local retag of an actual prior run rather than from
`initialConfig` on a raw pair input, so reaching it is neither halting of a composed
machine nor language acceptance; this module states no `accepts`, no `AcceptsAt` and no
language membership. Clock composition, the fixed parser, advice freedom, `NP` membership
and `ContentVerifierBridge` stay out of scope. Nothing here is P-vs-NP mainline progress.

**Part A G2p-e, iterating the gamma payload round (infrastructure only).** New pnp3
module `Complexity.Uniform.V1.FixedGammaTargetPayloadIteration`. There is **no new
machine**: the landed G2p-d `FixedGammaTargetPayloadRound.machine` re-enters `qLoop`
at the end of a round, so the *same* fixed 22-state, 66-row table iterates, and
`check_machine_reused` records that identity. Write `N = a+m`.

What is new. `round_generic` carries the loop invariant `loopTape B x w zeros r` from
`r` to `r+1` for **every** index with `1 ≤ r` and work remaining (`r < zeros`), out of
an **arbitrary** configuration matching the `r`-instance rather than out of
`startConfig`. That double quantification — over the index and over the incoming
configuration — is exactly what the hard-coded `r = 2 → r = 3` theorem could not
support, and it is what makes an induction possible. Its hypotheses are a matching
tag, `gammaZeros? (Fin.append x w) = some zeros`, `1 ≤ r`, `r < zeros`, that index's
own room `a+m+2+r < tapeLength (pairLength a m) B`, and the three projections of the
incoming configuration (`qLoop`, head `8+zeros+walk N zeros r`, tape
`loopTape B x w zeros r`); its conclusion is state, head and the whole tape after
exactly `roundClock N = 2*N-7` steps. The cost stays length-only at every index
because every `r`-dependence cancels. A round is a counter phase costing
`2*walk N zeros r + 2*(zeros-r) + 3`, a register walk out and back costing `2*(r+1)`,
a content carry out and back costing `2*(N-9-zeros-r)` that only the physical shape
performs, and six fixed steps. In the physical shape `walk = r`, so the counter phase
is already free of `r` and the carry's `-2*r` cancels the register walk's `+2*r`; in
the virtual shape there is no carry, `walk` is the constant `N-9-zeros`, and it is the
counter phase's `-2*r` that cancels the register walk. Both shapes take the same six
fixed steps; three of the virtual ones pass through the `qVa`/`qVb`/`qVc` padding,
standing at the positions where the physical shape enters `qClear`, `qCarry` and
`qBackCont`.
`check_round_generic_subsumes_round_step` derives the landed hard-coded `round_step`
statement back out of `round_generic` at `r = 2`, so the generic round is a strict
generalisation of the landed one rather than a parallel claim beside it.

`rounds_iterate` is the induction: at `2 ≤ zeros`, `2+k ≤ zeros` and the room every
round needs, running the same machine for exactly `k * roundClock N` steps out
of the landed G2p-d `startConfig` reaches the `r = 2+k` instance. `register_complete`
is its `k = zeros-2` instance: after exactly `loopClock N zeros = (zeros-2)*roundClock N`
steps the register `[N+1, N+1+zeros]` holds all `zeros+1` digits
`registerBit x w zeros j`. `register_digits` spells those out — digit `0` is the
bootstrap's leading `true` and digit `i+1` is the payload cell `9+zeros+i` read through
the blank padding, so `i < zeros` covers exactly the payload block
`[9+zeros, 9+2*zeros)` and a truncated payload contributes virtual zeros; "exactly" is
its own conjunct, an iff pinning those source addresses as precisely that block. That is
register **content** at an exact time, not a decoded number: no theorem here mentions
`contentHeader?` or any parsed header value.

Room and clocks. `room_iff` reads the iteration's room premise
`N+1+zeros < tapeLength (pairLength a m) B` as `zeros ≤ a+B` — the premise the G2p-d
round slice recorded as "assumed nowhere" — while a single round at index `r` assumes
only `r < a+B`; at `3 ≤ zeros` the iteration premise implies the round's `3 ≤ a+B` and
at `2 ≤ zeros` the foundation's `2 ≤ a+B`. Those premises are sufficient and used —
each round's trace reaches `N+2+r` and writes there, the largest such cell over the
rounds iterated being `N+1+zeros` at `r = zeros-1` — but nothing proves them
necessary: there is no footprint theorem here, and the deferred exhaustion finish has
none either, so nothing claims this to be the room a *complete* loop needs. `qLoop`
does **not** absorb, so every endpoint above is an *exact* time and may not be
transported past it; no deadline is exported and no first-arrival or strictness
direction is proved. None of these clocks counts the steps `startConfig` embeds, so
none clocks a composed pipeline.

Probes. Nonvacuity is independent of the endpoint theorems: two literal probes first
identify the phase-local start configuration for every budget from the landed G2p-d
foundation endpoint alone, then reduce the round machine's own `run` by kernel
computation at `B = 0` for **two** consecutive rounds. Both words decode to
`zeros = 4`, so exactly two rounds remain. The physical probe (`N = 17`,
`roundClock 17 = 27`, `loopClock 17 4 = 54`) pins round one's physical source `15`
with its `false` carried in the control as `qClear0`, the round-one re-entry into
`qLoop` on the advanced terminator `15` with a `false` appended at `21`, then round
two's `qCntMark` on counter cell `11`, its physical source `16` with the `true`
carried as `qClear1`, and the final register `[18,22] = true, true, false, false,
true` — so the two rounds drive both carried-bit halves of the table. The truncated
probe (`N = 15`, `roundClock 15 = 23`, `loopClock 15 4 = 46`) pins the virtual
schedule at both round endpoints: the terminator is at `14` after each round and the
corresponding appended register digits are false. In round two it additionally pins
the boundary source `15` and entry through `qVa`/`qVb`/`qVc`; the final register is
`[16,20] = true, true, false, false, false`.
`check_probe_inputs_valid` states separately that both probe words satisfy the
tag/width hypotheses the general theorems assume, and at the probes' own budget
`B = 0` the room hypothesis too, so those are not statements about an unsatisfiable
premise set.

Deferred: the exhaustion finish — at `r = zeros` the next round's counter scan finds
the marked cell `7+zeros` and leaves `qLoop` through `qFin`, and that behaviour,
`qDone`, and the restoration of the gamma zero field are outside every theorem here —
the loop's own deadline, a first-arrival/strictness direction, the decrement from
`n+1` to `n`, the all-times clamp/footprint/budget package, and every converse:
nothing says that `qLoop` at `loopClock N zeros`, or any register digit, implies
anything about `zeros`. `zeros = 2` is covered only degenerately (`loopClock N 2 = 0`
makes `register_complete` a restatement of the retagged foundation endpoint
`startConfig`) and `zeros ≤ 1` is excluded by `2 ≤ zeros`. No pnp4 bridge exists for
this module; `startConfig` is a phase-local retag of an actual prior run, not a
composed execution from the raw pair input, and `qDone` is not language acceptance.
Nothing here is P-vs-NP mainline progress.
The exhaustion finish deferred here — the stopping rule, `qDone`, and the restoration of
the gamma zero field — is discharged by the G2p-f slice above, together with a
first-arrival/strictness direction and an all-times clamp for that phase (the clamp only
because `qDone` absorbs, which `qLoop` does not; minimality comes from that phase's
closed-form schedule instead). A *length-only* loop deadline, the decrement from `n+1` to
`n`, a footprint/budget theorem and every converse still stand — G2p-f's
`payload_exhausted` does export persistence from `totalClock N zeros`, but that clock
depends on the decoded width. G2p-f adds no room premise of its own: it inherits this
slice's `zeros ≤ a+B`, and its `payload_exhausted` does claim that room *sufficient* for a
complete loop with the finish included, so the sentence above — that nothing claims this to
be the room a *complete* loop needs — now holds of *necessity* only, which no footprint
theorem establishes.

**Part A G2p-d round, first remaining payload digit (infrastructure only).** New
pnp3 module `Complexity.Uniform.V1.FixedGammaTargetPayloadRound`: one fixed
22-state, 66-row machine — every row pinned literally, and restated literally again
in its surface test — that executes **one** round of the self-stopping gamma
payload loop whose markers the G2p-d foundation installed. It is one round, not the
loop: the iteration, the exhaustion finish and the loop's own deadline are
deferred. Write `N = a+m`. `startConfig` definitionally retags the *actual* G2p-d
`FixedGammaTargetPayloadLoopFoundation` configuration at that phase's own
length-only deadline, replacing only the control field; `handoff_exact` pins head
and tape to that endpoint. So this is a real phase-local provider, not one fixed
machine running from the raw pair input, and `roundClock N = 2*N-7` is this phase's
cost alone and omits every step inside the start configuration; clock composition
remains out of scope.

What the round does. The foundation left the tape in the `r = 2` instance of the
loop invariant `loopTape B x w zeros r` — counter prefix `[8,7+r]` marked, trail
`[8+zeros, 8+zeros+walk N zeros r)` blank, walking terminator at
`8+zeros+walk N zeros r`, register `[N+1,N+1+r]` holding its `r+1` digits — and
`round_step` carries that invariant to `r = 3`. Under a matching tag,
`gammaZeros? (Fin.append x w) = some zeros` with **`3 ≤ zeros`** (work remains) and
the round's own room `a+m+4 < tapeLength (pairLength a m) B`, after exactly
`roundClock (a+m)` steps the machine is back in `qLoop` at head
`8+zeros+walk (a+m) zeros 3` with the whole tape equal to `loopTape B x w zeros 3`.
The round tests the tape counter (`qCntL`/`qCntZ` scan left over the blank trail
into the gamma zero field), marks the first unconsumed zero, cell `10`, walks back
to the terminator, reads the next source, **appends** its bit to the register at
cell `N+2+r`, and advances the walking terminator when the source was physical.
Every branch is decided by the symbol under the head: no width, digit index, target
address, proof term, advice or producer mark enters the control. It carries only the
scanned source result: a physical bit until its write, and the physical-versus-blank
branch until `qLoop` re-entry. There is no arithmetic carry —
the register write is an append, and the decrement from `n+1` to `n` stays a separate
deferred phase; `qCarry_b` names that held source bit.

Source, clock and room. The source is the third payload digit, index `2` of the
block `[9+zeros, 9+2*zeros)`, i.e. the cell `11+zeros`, and there is such a digit
exactly when `3 ≤ zeros` — which is also what makes cell `10` an *unconsumed* gamma
zero, so the counter can grow. `source_pins` states the address direction only: with
`11+zeros < N`, `sourceCell N zeros = 11+zeros`, and with `N ≤ 11+zeros` it is the
boundary blank `N`. In the latter branch `round_step` leaves the terminator unmoved,
while `registerBit_source` identifies the appended digit as virtual `false`.
`roundClock N = 2*N-7` is **length-only** and
identical in both shapes: the virtual branch's `qVa`/`qVb` are pure padding, which
is what makes the cost independent of the source shape and of the width. It is an
*exact* time and not a time from which the endpoint persists — `qLoop` does not
absorb — so no deadline is exported and the endpoint may not be transported later.
Room is strictly wider than the foundation's because the register grows:
`room_iff` reads `a+m+4 < tapeLength (pairLength a m) B` as `3 ≤ a+B`, one cell more
than `2 ≤ a+B`; this is sufficient for the proved run, whose head reaches `N+4` and
writes there, and implies the foundation premise so the handoff stays available. By
the proof's table trace (not an exported all-times theorem), the decoded-width
`round_step` path never goes below cell `9`: the tag prefix and first counter mark,
cell `8`, are never scanned, while cell `9` stops `qCntZ`. `malformed_rejects` covers the retag of a failed gamma
scan: the retagged foundation rejection rejects again in one step, room-free, at the
boundary head (cell `8` when `a+m = 8`), on the unchanged content tape — with no
first-arrival direction and no converse.

Probes. Nonvacuity is independent of the endpoint theorems: two literal probes
first identify the phase-local start configuration for every budget from the landed
G2p-d foundation endpoint alone, then reduce this machine's own `run` by kernel
computation at `B = 0`. The physical probe (`zeros = 3`, `N = 15`) pins the third
counter mark at cell `10`, the head on the source cell `14`, the `true` it reads
carried in the control as `qClear1`, the vacated cell `13` blanked, the appended
digit written at `N+4 = 19`, a still non-terminal `qBackCont` one step before the
end, and the halt-free re-entry into `qLoop` at step `23 = 2*15-7`. The virtual
probe (`zeros = 3`, `N = 12`, `walk N 3 2 = 0`) pins the opposite schedule: the
source address is the boundary blank `12`, the padding states `qVa`/`qVb` are
entered, the appended digit at `N+4 = 16` is the virtual `false`, and `qLoop` is
re-entered at step `17` on the *unmoved* terminator `11`.

Deferred: the iteration of this round, the exhaustion finish that restores the
gamma zero field (`3 ≤ zeros` excludes `qFin` only during the first `roundClock N`
transitions, the exact `r = 2 → r = 3` segment), the complete target register,
the loop's own deadline, a cell-by-cell `r = 3` layout theorem (the endpoint is
already a full tape equality to the public `loopTape`, whose `r = 2` layout the
foundation pins), a first-arrival/strictness direction for the round, the all-times
clamp/footprint/budget package, the decrement from `n+1` to `n`, the room a full
loop needs (`N+1+zeros < tapeLength (pairLength a m) B`, assumed nowhere), and the
degenerate widths `zeros ≤ 2`. No converse is stated: nothing says that `qLoop` at
`roundClock N`, or the digit at `N+4`, implies `3 ≤ zeros`. Nothing here is
connected to `contentHeader?` or to any parsed header value and no pnp4 bridge
exists for this module. The public `startConfig` at `zeros = 2` can follow exhaustion
through `qFin` to `qDone`, but `zeros ≤ 2` and exhaustion remain outside the proved
theorem surface; `qDone` is not language acceptance. Nothing here is P-vs-NP mainline progress.
Three of those deferred items are discharged above: the iteration of this round and the
complete target register by G2p-e, and the exhaustion finish that restores the gamma zero
field by G2p-f. A fourth moves rather than closes: the premise
`N+1+zeros < tapeLength (pairLength a m) B` recorded here as assumed nowhere is now
assumed and characterized (`zeros ≤ a+B`), and G2p-f's `payload_exhausted` proves it
*sufficient* for a complete loop with the exhaustion finish included; whether that much
is *necessary* is still open, there being no footprint theorem. A fifth shrinks: of the
degenerate widths deferred here, `zeros = 2` is now inside G2p-f's `payload_exhausted`,
which needs only `2 ≤ zeros`, so only `zeros ≤ 1` stays outside the proved surface. The
rest still stand — a *length-only* loop deadline among them, since G2p-f's exported
persistence is from the width-dependent `totalClock N zeros` — including the two items
G2p-f discharges for its own phase only: the first-arrival/strictness direction and the
all-times clamp hold for the finish, where `qDone` absorbs, and not for this round, whose
endpoint sits in the non-absorbing `qLoop`.

**Part A G2p-d loop markers, foundation slice (infrastructure only).** New pnp3
module `Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation`: one fixed
14-state, 42-row machine — every row pinned literally — that installs on the tape
the two markers a *self-stopping* gamma payload loop needs, and halts as soon as
they are in place. It is the finite preamble of that loop, not the loop: the round,
its iteration and the exhaustion finish are deferred. Write `N = a+m`. The target
register grows from scratch cell `N+1`; G2p-a wrote the leading `true` of `n+1`
there, G2p-b the first payload digit at `N+2`, G2p-c the second at `N+3`, so at a
decoded width `2 ≤ zeros` — the only width this slice proves anything quantified
about — exactly two payload digits, `9+zeros` and `10+zeros`, are consumed when
this phase starts, a constant of the phase ABI rather than data read off the tape;
the degenerate widths have consumed fewer, one at `zeros = 1` and none at
`zeros = 0`, the payload having fewer than two digits there. The markers are (i) a
**counter** inside the gamma zero field, a consumed zero rewritten
`some true` **left to right**, so that scanning left from the terminator
the first non-blank cell is an unconsumed zero while work is left and the last
consumed marker when the payload is exhausted — right-to-left marking would be
indistinguishable from tag cell `7`, which is also `some false` — and (ii) a
**walking terminator**, the `some true` at `8+zeros` moving one cell right per
*physical* source consumed with the vacated cell blanked, so the cell right of the
terminator is always the next source. `startConfig` definitionally retags the
*actual* G2p-c `FixedGammaTargetSecondPayload` configuration at the G2p-c
deadline, replacing only the control field (`handoff_exact` pins head and tape).
`markers_installed`: on a matching tag, `gammaZeros? = some zeros`, `2 ≤ zeros`,
and the inherited G2p-c room `a+m+3 < tapeLength (pairLength a m) B` (four
hypotheses), the machine has from step `exactClock zeros = zeros+7` on halted in
the absorbing `qDone` at head `8+zeros+walk (a+m) zeros 2` with tape
`loopTape B x w zeros 2` — the gamma zeros at `8` and `9` marked, the terminator
trail blank, the walking terminator installed, the three inherited register digits
untouched — and `markers_strict` excludes both terminal states at every earlier
step, so `zeros+7` is the *first* terminal time. `walk N zeros r =
min r (N-9-zeros)` covers the three source shapes in one closed form: both
consumed sources physical (`10+zeros < N`, terminator to `10+zeros`), only the
first physical (`10+zeros = N`, terminator to `9+zeros`), neither (`9+zeros = N`,
terminator unmoved); a virtual source costs the same three steps as a physical one,
which is what keeps the clock width-only. The advance is destructive only as far as
it moves, so the writes are shape-dependent: the both-physical shape overwrites
`9+zeros` and `10+zeros` with `some true` and blanks the first again, the middle
shape overwrites only `9+zeros` as the new terminator, and the tight shape
overwrites neither; the input terminator cell `8+zeros` is blanked exactly when
`9+zeros < N`, which is how `loopTape_layout` states it (a conditional conjunct, not
an unconditional one). The endpoint tape is therefore not `contentTape`, and
`loopTape_layout` pins it cell by cell (both marks, the conditionally blanked input
terminator, the walking terminator, the three register cells, blanks past `N+3`, and
the untouched tag prefix `[0,6]`). `markers_at_deadline` restates the endpoint at the
phase's length-only `deadline N = N`, and `malformed_rejects` inherits the G2p-c
rejection in one step, room-free. Room is inherited rather than needed: the head
never moves past `N`, which every budget allocates, so no `.right` move of this
phase can clamp; the premise (`room_iff`: `2 ≤ a+B`) is what makes the incoming
tape known and what allocates the register cells. Nonvacuity is independent of the
endpoint theorems: for both extreme shapes plus width zero, width one and a
malformed gamma, the surface tests first identify the phase-local start
configuration for every budget from the landed G2p-c endpoint theorems alone, then
reduce this machine's own `run` by kernel computation at `B = 0`. Deferred: the
round (counter test, source read, carry, register write), its iteration, the
exhaustion finish, the complete target register, the intended loop's own deadline,
the all-times clamp/footprint/budget package, the decrement from `n+1` to `n`, the
room a full loop needs (`N+1+zeros < tapeLength (pairLength a m) B`, assumed
nowhere), and the *quantified* endpoints of the two degenerate widths — where this
machine halts after two steps (`zeros = 0`) and after five with its counter mark
restored (`zeros = 1`), which is exercised here only by the literal probes at
concrete inputs — together with `malformed_strict`, the first-arrival direction of
the malformed branch, which this slice does not prove. The two surface obligations this slice
owed to the next one are now discharged by the G2p-d round slice above: all 42
table rows are restated literally in `check_table_rows` of the foundation's surface
test, and the 14 `Fin` state constants have direct `#print axioms` entries instead
of being reached only through `raw`/`machine`.
This foundation is **not** connected to `contentHeader?`: no theorem mentions a
decoded header field and no pnp4 bridge exists for it; `qDone` is an internal
endpoint, never language acceptance. Nothing here is P-vs-NP mainline progress.

**Part A G2p-c3 second-payload `contentHeader?` semantic bridge (infrastructure
only).** The pnp4 module
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetSecondPayloadBridge`
reads the landed G2p-c register against the parsed content header. Write
`N = a+m`. It has exactly four public theorems, all one-way implications out of
a decoded `contentHeader? = some (n, consumed)` and no converse anywhere; only
the last three reach a machine conclusion, because the first is machine-free.
`header_digits` is generic and machine-free — one hypothesis, any
`z : PrefixBitVec N`, no tag: a decoded header fixes `zeros` with
`gammaZeros? z = some zeros`, `consumed = 2*zeros+1`,
`2^zeros ≤ n+1 < 2^(zeros+1)`, the leading digit `(n+1).testBit zeros = true`,
and, for **every** `t < zeros`, the payload cell `9+zeros+t` read as
`(physicalSymbol z (9+zeros+t)).getD false = (n+1).testBit (zeros-1-t)`. The
`getD false` and the `t < zeros` guard are both load bearing: the decoder reads
its payload window through a virtual zero tail, so a payload cell at or past the
physical word is the digit `0` rather than a physical cell, and past the window
the truncated index `zeros-1-t` would repeat digit `0` at an address outside the
block. The other three theorems are about the landed machine at its
length-only, **phase-local** deadline `2*N`. Under a matching tag, a decoded
header with `3 ≤ n`, and exactly the room
`a+m+3 < tapeLength (pairLength a m) B` (four hypotheses), some `zeros ≥ 2` has
the header bounds above and the endpoint is `qDone` at head `7` on
`secondPayloadTape` with both digits taken from that same header, with cells
`N+1`, `N+2`, `N+3` holding `(n+1).testBit zeros`, `(n+1).testBit (zeros-1)`,
`(n+1).testBit (zeros-2)` — the three leading binary digits of `n+1`. Under a
matching tag and `consumed = 3`, with only the G2p-b room
`a+m+2 < tapeLength (pairLength a m) B` (three hypotheses), the two-digit G2p-b
register survives and every *allocated* cell past `N+2` stays blank, so no third
digit is written. Under a matching tag and the header `(0,1)` (two hypotheses)
the one-digit G2p-a register survives, with no room premise. Given a
decoded header the premise `3 ≤ n` is exactly `2 ≤ zeros`, since the exported
bounds make `zeros` the index of the leading digit of `n+1`; that equivalence is
derivable from the exported conjuncts and is *not* stated as an equivalence
theorem. The three concrete header hypotheses — `3 ≤ n`, `consumed = 3`, and
the header `(0,1)` — are jointly exhaustive over decoded headers, since
`header_digits` splits them by width: `zeros = 0` forces the header `(0,1)`,
`zeros = 1` forces `consumed = 3`, and `2 ≤ zeros` forces `3 ≤ n`. That coverage
is not free: the width-one branch assumes the G2p-b room and the positive branch
the wider one. Room, by contrast, is not implied by
the header — `room_iff` reads it as `2 ≤ a+B`, a condition on the `x` side and
the budget that a decoded header does not constrain — so `hroom` stays an
explicit premise. This bridge states no `qReject` theorem at all, and not for
want of room in one direction: on a matching tag,
`contentHeader? = none → qReject` at this deadline is already room-free from the
imports (`fixedGamma_header_contract` plus `malformed_at_deadline`, which takes
no room premise). What needs room is
the opposite direction, hence the `qReject ↔ contentHeader? = none` equivalence
that G2p-a states for the bootstrap: excluding `qReject` on a decoded header of
width one or more runs through the endpoint theorems, which assume `N+2` and
`N+3` allocated. `deadline` and `exactClock` remain phase-local: `startConfig`
retags the *actual* G2p-b endpoint configuration and embeds every earlier step,
which neither clock counts, so nothing here is a `UniformP` execution, a
runtime, or a clock for the composed pipeline. Nonvacuity is theorem-derived
rather than an independent machine reduction: for every budget, the probes pin
the one-digit register for header `(0,1)` (digit at cell `10`, with cell `11`
and every later allocated cell blank), `11₂` at cells `12,13` with cell `14`
still blank for `(2,3)`, `100₂` at `12,13,14` for `(3,5)`, `110₂` at `13,14,15`
for `(5,5)` (second payload digit the virtual zero at the boundary), and `111₂`
at `14,15,16` for `(6,5)` (second payload digit physical). No pnp3 machine,
source, or test file changed in this slice; only pnp3 documentation.
Deferred: the remaining `zeros-2` digits, the decrement of the stored `n+1` to
`n`, parser execution, `contentInput?`, `ContentAccepts`, language acceptance
from `qDone`, the raw-input composed machine and its clock, the all-times
footprint/budget package, `ContentVerifierBridge`, advice-freedom, and `NP`
membership. Nothing here is P-vs-NP mainline progress.

**Part A G2p-c2 second gamma payload digit, positive-width execution
(infrastructure only).** `FixedGammaTargetSecondPayload` now runs its fixed
14-state, 42-row control on the `2 ≤ zeros` route and proves that the second
gamma payload digit is copied into the target register. Write `N = a+m`. The
premises are explicit and satisfiable: a matching tag
(`tagMatches (Fin.append x w) = true`), a *decoded* width
(`gammaZeros? (Fin.append x w) = some zeros`) with `2 ≤ zeros`, and exactly the
room the run needs, `a+m+3 < tapeLength (pairLength a m) B` — equivalently
`2 ≤ a+B` by `room_iff`, so it fails at `a = B = 0` and at `a+B = 1`. Under
those premises `second_payload_exact` gives, for **every** `s` with
`exactClock N zeros = 2*N-7 ≤ s`, the endpoint state `qDone`, head `7`, and the
whole tape equal to `secondPayloadTape B x w b0 c`: every content cell restored,
the blank boundary at `N`, the register `true` at `N+1`, the G2p-b digit `b0` at
`N+2`, the second digit `c` at `N+3`, and blanks after `N+3`
(`secondPayloadTape_layout`). `second_payload_strict` excludes *both* terminal
states for every `s < 2*N-7`, so `2*N-7` is the **first** terminal time: the
former design constant is now derived row by row rather than assumed, and it is
the same value in all three shapes of the route (both payload cells physical,
source cell exactly at the boundary, first payload cell already at the
boundary). The copied value `c` is the *content* symbol at the logical source
address `10+zeros`, the second payload cell of the block `[9+zeros, 9+2*zeros)`
— `second_source_cell` pins `10+zeros = 9+zeros+1` and places it inside the
block under `2 ≤ zeros`, that direction only and with no converse — so `c` is
`(physicalSymbol (Fin.append x w) (10+zeros)).getD false`. That endpoint is
extensional, and the three shapes realize it by three different schedules. When
`10+zeros < N` the source is physical and the control really does read it: the
run steps *over* the first payload cell `9+zeros` in `qStepOne` and reads
`10+zeros` in `qRead`, and that bit is copied verbatim (`second_physical_exact`,
premise `physicalSymbol (Fin.append x w) (10+zeros) = some b`). When
`10+zeros = N` the source address *is* the blank boundary, so `qRead` is entered
and scans that blank, taking the virtual zero. When `9+zeros = N` the *first*
payload cell is already the blank boundary, so `qStepOne` reads *that* blank and
hands straight to the register: `qRead` is never entered, and `10+zeros` is then
`N+1`, the register cell — the head passes it, but in `qReg0` and over a tape
holding the register `true`, which is crossed rather than read as a source. Both
virtual shapes copy `false` (`second_virtual_exact`, premise `a+m ≤ 10+zeros`),
which is what `Option.getD` records for a `none` content symbol. Neither the
register `true` at `N+1` nor the G2p-b digit at `N+2` is ever taken as the
source: both are crossed in the register state that the selection already
fixed. Two more exports cover the local fit obligations of this branch:
`positive_width_head_range` bounds the head by `[7, N+3]` at every time, and
`positive_width_no_boundary_clamp` shows that no transition of the run clamps at
either tape end — the head *enters* the last allocated cell of the run, `N+3`,
on the preceding right move out of `N+2`, and the transition taken *at* `N+3` is
the write, which moves left, so no right move is attempted from the last cell.
Both are head facts, not a footprint: they say nothing about which cells may
differ from the incoming tape. The all-times footprint (`which cells differ`)
and `budget_independence`
remain deferred for every branch of this module. Scope caveats are unchanged and
still binding: `startConfig` is a **phase-local handoff** that definitionally
retags the actual G2p-b `FixedGammaTargetFirstPayload` endpoint configuration at
the G2p-b deadline (`handoff_exact` pins head and tape), so the provider is real
rather than synthetic, but this is *not* one fixed machine running from the raw
pair input; the length-only deadline `2*N` and the exact clock `2*N-7` are this
phase's cost alone and omit every step embedded in the start configuration;
clock composition stays out of scope; `qDone` is an internal endpoint, not
language acceptance; and no theorem has a converse — nothing here says that
`qDone`, or a written digit, implies `2 ≤ zeros` or a well-formed gamma.

The foundation of the same module is unchanged. This slice is the second part of
the G2p-c second-payload specialization (a separate line of work from the
generic payload round); the G2p-c1 part landed the table, the phase-local input
ABI, exact room, the phase-local clocks, and the two decoded widths at which the
machine provably makes no net payload or register write and leaves the tape
unchanged end to end (the anchor *is* blanked in flight and restored, so what is
proved is the absence of a net tape change). No width, digit index, bit, target
address, proof term, or clock enters the control; the eight positive-route
states (`qSeekTerm`, `qStepOne`, `qRead`, `qCarry0`, `qCarry1`, `qReg0`,
`qReg1`, `qBackReg`) that the foundation slice landed without exercising are
exactly the states the positive-width trace above now runs. The machine blanks
the tag cell `7` as its single anchor and steps onto cell `8`: a terminator at
`8` is width zero and a terminator at `9` is width one, and in both cases it
turns around, restores the anchor, halts in `qDone` at head `7`, and hands back
the tape it was handed unchanged. For those two widths the private traces keep
the head in `[7,9]`, but that read bound is internal: what is exported there is
the tape equality, which pins the net effect of the run and not the cells it
visited. The two sweeps have different delimiters: only the leftward `qScanLeft`
sweep is delimited by a cell the run maintains (the blanked anchor at `7`); the
rightward sweep is delimited in phases by cells the run maintains none of — the
input terminator at `8+zeros` ends the `qSeekTerm` scan at every width, and on a
positive width the layout blank at `N` then ends the walk across the content and
the first blank after the register, the target cell `N+3`, ends the register
walk, that last delimiter being consumed by the write rather than maintained.
Exports: all 42 rows pinned literally with the resource counts; the phase-local
handoff; `room_iff`; `exactClock` with values `3`, `5`, `2*N-7` by *decoded*
width, **all three** of which are now proved exact first arrivals (endpoint from
that time on, plus exclusion of both terminals before it); a malformed gamma has
no decoded width and is clocked separately by `malformedExactClock = 1`, which
`malformed_exact` and `malformed_strict` together prove to be its first terminal
time; `exactClock_le_deadline` under `3 ≤ N` (sharp at width one, and free in
scope since `N ≥ 9+zeros ≥ 11` on the positive branch); and full
state/head/tape endpoints for malformed, width zero, width one, and now the
positive width. The width-one endpoint additionally proves that every
*allocated* cell after `N+2` is blank, the target cell `N+3` included whenever
it is allocated — its premise allocates only `N+2`, so that claim is vacuous
exactly when `N+3` does not exist. Room premises stay exact per width and are
never inferred from a decoded header: width zero needs none, width one needs
only the G2p-b premise `a+m+2 < tapeLength (pairLength a m) B`, and the positive
width needs `a+m+3 < tapeLength (pairLength a m) B`. No theorem covers a width
without its premise, so nothing here says that `qReject` implies a malformed
gamma. Independent literal reduction probes identify the actual start
configuration for five concrete inputs from the landed G2p-b endpoint theorems
and then reduce this machine's own run by kernel computation, without invoking
any endpoint theorem of this module. Of the three foundation probes, the
width-zero and width-one probes pin the width dispatch at cells `8`/`9` and the
anchor blank and its restoration, the width-one probe alone also pins the target
cell `N+3` — which every one of these five inputs allocates — still blank at the
endpoint, and the malformed probe pins instead that the handed-over
configuration is in neither terminal state and that one step rejects in place at
the boundary head. The two positive-width probes walk the whole route in its two
extreme shapes. The physical probe (`zeros = 2` at `N = 13`) pins
`qStepOne` over the first payload cell, `qRead` at the source cell `12`, and the
`qCarry1` that records the source bit. The tight probe (`zeros = 2` at `N = 11`,
both payload digits virtual) pins the opposite schedule: `qStepOne` reads the
blank first payload cell and the next step is already `qReg0` at `12 = N+1`, so
`qRead` is never entered and the register `true` that its endpoint pins at that
address is crossed rather than read. Both then pin the head on the still-blank
target cell at step `N-4`, the digit written by the transition taken there and
visible at step `N-3`, a non-terminal control at step `2*N-8` — which, both
terminal states being absorbing, also excludes any earlier terminal arrival —
and the halt at step `2*N-7`. The `contentHeader?` reading of these endpoints is
now supplied outside pnp3, by the G2p-c3 bridge described above; this module
itself still states no pnp4 reader or parser fact and needed no change for it.
Deferred: the remaining `zeros-2` digits, the decrement to `n`, the all-times
footprint/budget package, parser execution, and `ContentVerifierBridge`. This is
a specialization, not an iterating round: the same rows cannot walk a general
payload, because that needs both a counter and an advancing source marker,
neither of which this control has. Nothing here is P-vs-NP mainline progress.

**Part A G2p-b first gamma payload bit (infrastructure only).**
`FixedGammaTargetFirstPayload` is a fixed 18-state, 54-row machine whose start
configuration only retags the actual G2p-a bootstrap configuration at the
bootstrap deadline; no width, bit, index, or proof enters the control. Write
`N = a+m`. The target register is filled most significant bit first from scratch
cell `N+1`, where the bootstrap wrote the leading `true` of `n+1`; this slice
adds its second digit at `N+2` and nothing else. On a matching tag the machine
blanks the terminator `8+zeros` as a marker and cell `7` as an anchor. Width
zero restores both without reading cell `9` and needs no room. Positive width
reads the payload cell `9+zeros`: a physical `some b` is carried as `b`, and
the blank boundary (`9+zeros = N`) as the virtual `false`. The machine steps over
the scratch `true` at `N+1` without reading it as source, writes the carried bit
at the target cell `N+2`, and restores the terminator and cell `7`. At the
length-only deadline `3*N` the endpoint is `qDone` at head `7`. For width zero
the tape is the bootstrap scratch tape. For positive width it is that tape with
the carried bit at `N+2`, under the exact premise
`a+m+2 < tapeLength (pairLength a m) B` (equivalently `0 < a+B`); the header does
not imply it, since it fails at `a = B = 0`. Malformed gamma ends in `qReject` at
head `N` on `contentTape`, with no room premise. All 54 rows are pinned
literally. At every time, clamp freedom and budget independence hold on every
tagged input whose positive gamma width has room (for both budgets in the
latter), and on decoded widths the head stays in `[6,8]` (width zero) or
`[6,N+2]` (positive width) with footprint `{7, 8+zeros, N+1, N+2}`, again
assuming room for positive widths. No theorem covers a positive width without
room, so nothing here says that `qReject` at this deadline implies malformed
gamma. The pnp4 companion
`ContentFixedGammaTargetFirstPayloadBridge` proves one direction for matching
tags. Suppose `contentHeader? z = some (n, consumed)` with `0 < n`
and the room premise. Then for some `zeros > 0` with `consumed = 2*zeros+1` and
`2^zeros ≤ n+1 < 2^(zeros+1)`, cells `N+1` and `N+2` hold `(n+1).testBit zeros`
and `(n+1).testBit (zeros-1)`. For the header `(0, 1)`, the register stays the
one digit of `1`. Unlike G2p-a, no exact first-arrival clock or strictness is
exported; only the length-only deadline is. The remaining `zeros-1` payload
digits, the decrement to `n`, clock composition, and `ContentVerifierBridge` are
not provided, and nothing here is P-vs-NP mainline progress.

**Part A G2p-a terminator-to-scratch bootstrap (infrastructure only).**
`FixedGammaTerminatorScratchBootstrap` is a fixed 9-state, 27-row machine whose
start configuration only retags the actual G2m dispatcher configuration at the
dispatcher deadline. Write `N = a+m`. On a matching tag it normalizes the
dispatcher heads `6`/`7` to cell `8` and scans the gamma zeros. It blanks the
physical terminator at `8+zeros` as a return marker (the only blank cell below
`N`), scans to the blank boundary `N`, and writes `true` at scratch cell `N+1`,
which exists for every budget. It then steps back over `N`, scans left to the
marker, restores the terminator, and halts in the absorbing `qTerm`. The first
terminal time is exactly `2*N-11-zeros` and the length-only deadline is `2*N`.
The endpoint head is `8+zeros`, and the endpoint tape is `contentTape` changed
only at `N+1`. A failed gamma scan rejects after one step. Every row is pinned
literally, and an explicit schedule gives the exact state, head, and tape at
every time. The module proves strict first arrival, the head window `[6, N+1]`
on successful runs, and clamp freedom and budget independence for every tagged
input and budget. The pnp4 companion
`ContentFixedGammaTerminatorScratchBootstrapBridge` proves two facts at that
deadline, for matching tags. The bootstrap rejects exactly when
`contentHeader? = none`. For a header `(n, 2*zeros+1)` the scratch cell holds
`(n+1).testBit zeros`, the leading binary digit of `n+1`. Only that digit is
written: the shuttle crosses the payload cells, but neither decodes nor copies
their digits. Nothing here claims
parser execution, content acceptance, untagged behavior, or P-vs-NP mainline
progress.

**Part A G2o dispatcher header-value bridge (infrastructure only).**
`ContentFixedGammaPayloadDispatcherHeaderValueBridge` adds seven public
theorems. Two hypothesis-free reader iffs, covering width zero and
out-of-range windows, say that `VirtualZeroTailReader.readNatBE` is `some 0`
exactly when `allZeroSlice?` is `some true`, and that `allZeroSlice?` is
`some false` exactly when the read is `some payload` with `0 < payload`. The
hypothesis-free, subtraction-free iff
`contentHeader?_eq_some_iff_gammaZeros_payload` says
`contentHeader? z = some (n, consumed)` exactly when, for some `zeros` and
`payload`, the physical scan gives `gammaZeros? z = some zeros`, the payload
read at logical length `2*N+1` over `[9+zeros, 9+2*zeros)` is `some payload`
(cells at or past `N` read as virtual zeros), `n+1 = 2^zeros + payload`, and
`consumed = 2*zeros+1`. The one-way
`contentInput?_target_eq_contentHeader` has the single premise
`contentInput? codec z = some pr` (any codec, no monotonicity or injectivity)
and yields some `consumed` with `contentHeader? z = some (pr.1, consumed)`
together with `pr.2.n = pr.1`, so on a successful parse the target read by
`ContentAccepts` equals the header target. Each dispatcher iff has the single
premise of a matching tag: at the common deadline, `qReject` holds exactly when
`contentHeader? = none`; `qAllZero` exactly when
`∃ n zeros, contentHeader? = some (n, 2*zeros+1) ∧ n+1 = 2^zeros`; and
`qHasOne` exactly when the same header shape has `2^zeros < n+1`. Width zero
(header `(0, 1)`) and virtual payload cells are included. The gamma width and
the payload natural are never identified with the header target; the parsed
target equals the header target only through a successful `contentInput?`.
Nothing claims that the dispatcher stores or materializes `n` or the payload,
that any machine executes the parser, that an endpoint is acceptance of the
content language, or anything about untagged input, uniform heads, clock
composition, `ContentVerifierBridge`, advice freedom, or NP membership; this is
not P-vs-NP mainline progress.

**Part A G2n total dispatcher semantic bridge (infrastructure only).**
`ContentFixedGammaPayloadDispatcherSemanticBridge` connects the fixed G2m
deadline classifier to the strict content reader at the shared logical length
`2*(a+m)+1`. On matching tags, `qAllZero` is equivalent to the existence of a
decoded gamma width whose exact payload scan is `some true`, `qHasOne` is
equivalent to the analogous `some false`, and `qReject` is equivalent to gamma
failure (also to gamma failure conjoined with `contentHeader? = none`). The
proof covers width zero, derives fit from `gamma_contract`, and constructively
identifies physical true with a true padded read. It does not identify decoded
values, payload naturals, acceptance, parser correctness, untagged behavior,
uniform heads, or cross-machine clocks, and is not P-vs-NP mainline progress.

**Part A G2m dispatcher deadline/classifier (infrastructure only).**
`FixedGammaPayloadDispatcherDeadline` gives the fixed G2k/G2l dispatcher the
transparent common deadline `2*N*N`, constructively partitions every decoded
gamma payload into first-true, first-virtual, or exhausted branches, and lifts
all exact endpoints by absorption.  On matching tags it classifies the total
deadline endpoint with branch-specific heads: malformed at `a+m`, zero width
at `7`, and cleaned positive paths at `6`.  The physical endpoint equivalences
say `qHasOne` exactly when a physical true occurs in the payload window,
`qAllZero` exactly when none occurs for valid gamma, and `qReject` exactly when
`gammaZeros? = none`.  This adds no pnp4 reader/parser semantics or acceptance
claim and remains infrastructure rather than P-vs-NP mainline progress.

**Part A G2l dispatcher positive rounds (infrastructure only).**
`FixedGammaPayloadDispatcherRounds` now proves the same-machine, zero-offset
positive physical-true, first-virtual, and full-false exhausted executions of
the fixed G2k dispatcher from its actual G2a-derived start configuration. The
strict cleaned endpoints restore literal content at head 6, and the public
guards exclude `k = 0` and the final `k = zeros` boundary from pending formulas.
No semantic iff, parser/decode theorem, length-only cap, or pnp4 claim is added.

**S11 one-gate acceptance closure (infrastructure only).** The single reviewed
unfreeze of the frozen TMVerifier tree added
`TuringToolkit/GateOneAcceptsClosure` and its literal probes, closing
acceptance of the one fixed gate machine for *every* request. The two
endpoints are hypothesis-free — the sole binder is `r : G1Request`:

```lean
g1CS_accepts_eq_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      r.spec.isSome

g1CS_accepts_iff_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.WellFormed
```

The first says the real `G1M` run, from the real initial configuration on the
standard encoded point and read after exactly its own unchanged
`g1Clock (encodeG1 r).length` steps, carries the accepting state exactly when
the pure result `r.spec` is defined; the second composes that with main's
pre-existing pure `spec_isSome_iff`, so the verdict is exactly
`r.WellFormed = r.Canonical ∧ r.operandsInBounds`. This is main's T1
transducer convention: a defined
`false` accepts exactly as a defined `true` does, because both output-done
handoffs enter the same literal accept state, and the result *value* sits on
the output cell rather than in the verdict. Among the nonaccepting requests
only the noncanonical class is a literal rejection; a canonical request with an
out-of-range operand idles at a `bOOB` boundary that is proved distinct from
both sinks. Acceptance is **exact-step, not halting** — no theorem says the
machine halts — and every statement is scoped to the image of `encodeG1`, so
nothing is claimed for a physical word outside that image and this is not a
language-membership theorem. No transition row, clock, step count, head
position, encoder or `GateN` declaration changed. This is one gate, not the
multi-gate chain: it is unrelated to the Part A uniform gamma track above, it
adds no `GateN`, `ContentVerifierBridge` or content-verifier claim, it reduces
no pnp4 source obligation, and it is not P-vs-NP mainline progress.

**Current engineering priority.** The one-tape `pnp3/Complexity/TMVerifier/`
tree is frozen at Git tree `b49456d6`, the subtree of commit `7b53a08f`; see
`pnp3/Docs/TMVERIFIER_FREEZE.md`, whose migration record covers the two
unfreezes since `42c59881` (the reviewed S11 one-gate acceptance closure, and
the single authorized GN-E2-3b body-driver slice, open as PR #1777: its
exact-head local `./scripts/check.sh`, its two independent read-only reviews,
the owner attestation and the `tmverifier-unfreeze` label are done, while the
remote gate results against the final head, the required PR review and a
history-preserving merge are still owed). Do not resume E2-4 or later
gate-by-gate construction. Active
model-repair work must use the versioned uniform complexity foundation outside
that tree.

**P1a/P1c uniform foundation (infrastructure only).** The independent namespace
`Pnp3.Complexity.Uniform.V1` provides finite `UniformTM` data with the distinct
symbols `some false`, `some true`, and blank `none`; same-budget exact/within
decision semantics; `polyClock`; a versioned `UniformP`; complement closure;
and an arbitrary-length parity scanner proving that input length is observable.
P1c explicitly codes the finite machines, proves the versioned `UniformP`
languages countable, and directly diagonalizes a length-only language outside
that class. See `pnp3/Docs/UniformP_V1.md`. This does not rebind, characterize,
or change the legacy canonical repository `P`/`NP`, define `UniformNP`, prove a
lower bound, or reduce a pnp4 mainline source obligation.

**P2-1 Uniform V1 pair codec (infrastructure only).**
`Complexity.Uniform.V1.PairEncoding` encodes `(x,w)` as false-tagged input
bits, one true separator, and the untagged witness.  Its executable structural
decoder has exact image, malformed-word, dependent roundtrip, and packed
cross-length injectivity theorems, plus direct initial-tape layout bridges.
The complete finite words are uniquely decodable, but the family is not
prefix-free because witness extension extends an encoding.  This slice adds no
relation/verifier or parser machine, does not define `UniformNP`, prove
`P ⊆ NP`, migrate canonical definitions, or reduce a pnp4 mainline obligation.

**P2-2 advice-free relation semantics / versioned `UniformNP` (infrastructure
only).** This slice defines one length-indexed `WitnessRelation`, its
total raw-word language through the P2-1 decoder, and `VerifiesRelation` over
every raw length and word at `polyClock verifierExponent N`. Malformed words
and false relation answers require literal rejection. `UniformNP` fixes one
relation, one finite machine, one verifier exponent, and an independent
witness exponent before inputs, with witness bound
`m ≤ polyClock witnessExponent n`. Named wrappers and paired axiom roots cover
all seventeen P2-2 theorems. Executable controls distinguish acceptance,
rejection, and timeout. This slice adds no parser machine,
`UniformP ⊆ UniformNP`, canonical `P`/`NP` rebind, pnp4 theorem, or lower-bound
claim.

**P2-3a fixed Uniform V1 pair-parser executable core (infrastructure only).**
`Complexity.Uniform.V1.FixedPairParserCore` adds one fixed ten-state parser,
its exact table/public-step bridge, exact `2*N+1` clock and `3*N+2`
exact-clock tape allocation, and only closed malformed/valid exact-run and
whole-tape-restoration capstones. The namespaced surface wrappers live in
`Tests.UniformV1FixedPairParserCoreSurfaceTests`, with paired direct/wrapper
roots in the central axiom audit. This slice proves no all-length parser
correctness, universal decoder equivalence, arbitrary-budget theorem,
parser/verifier composition, relation verification, `UniformP` inclusion,
gate bound, or P-vs-NP mainline result.

**P2-3b universal exact Uniform V1 pair-parser correctness (infrastructure
only).** `Complexity.Uniform.V1.FixedPairParserLanguage` gives independent DFA
and inductive-grammar semantics and proves their equivalence to dependent
`decodePair` success. `Complexity.Uniform.V1.FixedPairParserCorrectness` proves,
for every raw `y : Bitstring N`, the exact `clock N = 2*N+1` final state, strict
absence of either public terminal at every earlier step, head-zero and full
allocated-tape restoration, exact acceptance/rejection iff decoder
success/failure, exact `DecidesAt`, and only then derived `DecidesWithin`. The
proof has a dedicated empty-input root and positive-input forward/rewind
invariant roots. It introduces no parser/verifier composition, relation
verification, class inclusion or migration, pnp4 theorem, or circuit bound.

**P2-3cA ambient-budget fixed-parser transport (infrastructure only).**
`Complexity.Uniform.V1.FixedPairParserAmbient` relates the exact-clock tape to
every ambient budget `B` satisfying `clock N ≤ B` through explicit dependent
`Fin` embedding/projection and a four-clause blank-extension invariant. It
proves through-clock simulation of the same fixed parser, full ambient padding
blankness, exact final state/head/tape restoration, strict preterminality,
decoder-equivalent literal acceptance/rejection, and `DecidesWithin` using
`clock N` as an explicit witness. It introduces no configuration casts,
runtime advice, generic verifier budget theorem, parser/verifier composition,
relation verification, class inclusion, pnp4 theorem, or circuit bound.

**P2-3cB1 generic bounded budget transport (infrastructure only).**
`Complexity.Uniform.V1.BudgetTransport` proves for every fixed `UniformTM` that
a run of `s ≤ C` transitions from canonical head zero is a genuine blank
extension when the budget grows from `C` to `B`. The proof derives unit head
speed and strict right room at every pre-step `r < s`, so it does not assume an
unrestricted budget theorem. Exact-time accept/reject/decision predicates are
invariant, while within-budget predicates are transported only forward using
the same witness. This adds no provider, advice, machine family, combined
parser/verifier machine, relation/class theorem, pnp4 result, or gate bound.

**P2-3cB2 routed combined-machine constructor and parser handoff
(infrastructure only).** `Complexity.Uniform.V1.CombinedMachine` builds one
fixed machine from a fixed verifier `V` using exactly `8 + V.stateCount`
controls: eight nonterminal parser controls followed by all verifier controls.
Parser-accept rows restore cell zero and enter injected `V.start` in the same
transition; malformed/empty paths enter injected `V.reject`. The verifier side
maps `V.step`. Full same-budget verifier embedding, bounded parser-prefix
translation, successful full-configuration handoff, and literal malformed
rejection are proved. No host restart or extra handoff step exists. This slice
does not yet prove the total verifier suffix, relation verification, class
inclusion, pnp4 result, or gate bound.

**P2-3cB3 total combined correctness and relation packaging (infrastructure
only).** `Complexity.Uniform.V1.CombinedCorrectness` proves that the routed
machine executes one parser prefix of `2*N+1` steps and one verifier suffix of
`N^c+c` steps with no additional handoff. Malformed raw words remain literal
combined reject; successful words execute the embedded verifier at the same
ambient budget. The exact total clock is dominated by `polyClock (c+3)`, while
`c+2` fails at length one. Consequently every fixed verifier satisfying
`VerifiesRelation V c R` yields
`VerifiesRelation (combinedMachine V) (c+3) R` on all raw words. This is still
generic infrastructure: it does not construct the concrete tree-circuit
relation body, bridge to the legacy TM/framing model, prove class inclusion,
add a pnp4 theorem, or establish P versus NP.

**Part A P2-4a guarded content/tree witness relations (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.TreeCircuitContentWitnessRelation` packages
the content and tree-prefix semantic Booleans as distinct V1 witness relations,
rejecting every noncanonical certificate length. The content relation uses a
computable query-first concatenator; a separate proposition-level theorem
identifies it with canonical `concatBitstring`, whose historical definition is
noncomputable. This constructs no verifier machine, proves no equality between
the two semantic relations, supplies no `ContentVerifierBridge`, and establishes
no NP membership or lower bound.

**Part A G0-B1 explicit content-window cap (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixExplicitCap` derives transparent,
choice-free exponents directly from `thresholdPoly`, the concrete witness width,
and `treeMCSPPrefixM`. Under successful authoritative content semantics it bounds
both the header-designated window and the actual dependent parser target by
`N ^ contentCapExponent k + contentCapExponent k`. The exponent is executable
data fixed by `k`, not an existential witness or runtime advice. This does not
yet implement compressed virtual-zero-tail semantics, compile a verifier to V1,
or supply `ContentVerifierBridge`.

**Part A G0-B2a virtual-zero-tail reader core (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentVirtualZeroTailReaderCore` implements
the strict content readers and complete tree-prefix parser against a physical
source plus an independent logical extent, without constructing a padded
vector. Its whole-result theorems recover the frozen operations on `padWord`,
including every failure branch. This is the semantic reader/parser layer only:
it does not yet compute capped schedules, evaluate the concrete codec, construct
a V1 machine, prove a runtime bound, or supply `ContentVerifierBridge`.

**Part A G0-B2b1 capped arithmetic (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentCappedArithmetic` adds exact
success/overflow contracts for capped naturals, addition, multiplication,
binary length, and exponentiation by halving. It avoids evaluating an uncapped
power before checking its intermediates. These are source-level arithmetic
facts, not yet the concrete content-size record, bounded semantic verifier,
V1 machine, runtime proof, or `ContentVerifierBridge`.

**Part A G0-B2b2 concrete capped size records (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentCappedSizes` computes every concrete
threshold/table/witness/gamma/index/ambient field behind the merged cap-aware
arithmetic. Its exact `some` and strict-overflow `none` biconditionals tie the
executable pipeline to authoritative `treeMCSPPrefixM`; successful results also
retain `witnessBits ≤ M`, `tableLen ≤ M`, and cap corollaries. This does not yet
construct the bounded content parser/semantic verifier, a V1 machine, a runtime
proof, or `ContentVerifierBridge`.

**Part A G0-B2c bounded content semantic glue (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.BoundedContentSemanticVerifier` feeds the
merged capped `ContentSizes` result into the virtual-zero-tail parser at exact
logical extent `sizes.M`. Its strongest unconditional parser theorem is the
cap-filter characterization; plain parser equality is available only under a
target-fit or semantic-acceptance hypothesis. Its source-level Boolean checker
is proved extensionally equal to authoritative `contentSemanticAccepts`. This
still does not provide a fixed `UniformTM`, tape-level evaluator, runtime proof,
`VerifiesRelation`, or `ContentVerifierBridge`.

**Part A tagged/content framing ABI (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ThresholdTaggedContentFraming` explicitly
connects canonical V1 `encodePair` inputs to headerless authoritative
`contentSemanticAccepts` and makes malformed raw words evaluate to `false`.
This closes a proposition-level framing equation, not an operational tape
conversion. `CombinedMachine` still hands its verifier the unchanged tagged
word, so a fixed compactor/evaluator and blank-preserving legacy simulation
remain open.

**Part A fixed pair-concat sentinel phase (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairConcatSentinel` is a closed seven-state
`UniformTM` that preserves every input bit, writes a positional `some true`
marker at the first blank cell, and returns to head zero in exactly `2*N+1`
steps. Full-configuration, all-prefix footprint, budget-independence,
preterminality, literal acceptance, and `polyClock 2` decision theorems are
proved, including `N = 0` and budget zero. This is only the reusable marker
phase: it does not remove pair tags, compact `x ++ w`, evaluate the content
relation, or provide the legacy bridge. The all-budget exact theorem includes
budget zero; the exported blank-after-marker lookahead fact separately assumes
positive budget so cell `N+1` actually exists.

**Part A fixed separator cursor (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairSeparatorCursor` is a closed five-state
`UniformTM` that consumes the sentinelized tagged pair layout, validates the
alternating query tags, confirms a nonblank successor for the separator, and
halts with the head exactly on that separator in `2*n+2` steps. It preserves
the entire tape and proves an exact valid trace plus an exact positive-budget
malformed trace, footprint, budget-independence, no-clamp, and strict terminal
behavior. Separator-first
deletion is intentionally rejected because it can collapse different pair
splits to an identical configuration. This cursor locates the split but does
not yet remove tags or compact the headerless payload.

**Part A fixed separator-hole phase (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairSeparatorHole` is a closed three-state
one-transition machine whose standalone start is obtained by proof-level
retagging of the validated cursor handoff. It blanks only
the separator cell, and leaves the head on the resulting interior hole. Query
tags/data, witness, sentinel, and padding remain at their original addresses.
The hole is unique only through the sentinel (global uniqueness is false with
extra padding); the final Nat-indexed tape view is injective in the original
pair, so the separator-deletion collision does not apply. This phase does not
remove query tags, shift the witness, or complete headerless compaction.

**Part A fixed all-tag-removal phase (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairTagRemoval` is a closed nine-state
machine that repeatedly compacts query data rightward into the separator-hole
region. At exact clock `n*(n+5)+2`, the tape is
`[n+1 blanks][query][witness][marker]`: every query tag is gone and query plus
witness are physically contiguous, but the content block remains offset from
the origin. The phase proves exact full execution, footprint, budget
independence, strict terminal timing, right-clamp avoidance, and this
construction's single left-origin clamp. It does not yet shift the contiguous
block to cell zero, evaluate the content relation, or provide the legacy bridge.

**Part A fixed one-cell origin-shift bootstrap (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairOriginShiftBootstrap` is a closed
seven-state rolling-hole machine that shifts the entire contiguous
`query ++ witness ++ marker` block one cell left. At exact clock
`4*n + 3*m + 5`, it transforms `[n+1 blanks][query][witness][marker]` into
`[n blanks][query][witness][marker]`, preserving order and leaving no interior
hole. The final right command clamps exactly when `B = 0`; otherwise it moves
to the physical blank after the erased old marker. The phase proves exact
execution, first terminal, footprint, scoped cross-budget accounting, exact
layout, and fixed-extent recovery. It is not full origin alignment when
`n > 0`, and it does not claim that headerless concatenation recovers a varying
query/witness split.

**Part A fixed complete origin-alignment execution core (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment` is a closed 26-state
machine that repeatedly performs structural origin probes and stable whole-block
left shifts. At exact clock `(10*n + 7)*(n + m + 1) + 3*n`, it reaches literal
accept with head at cell zero and the complete tape
`[query][witness][marker][blanks]`. The machine uses no runtime counter or
advice and never identifies the marker by its Boolean value. This foundation
slice proves the exact predecessor handoff, fixed table/resources, polynomial
clock identity, and exact full-configuration run. First-terminal, post-clock,
footprint, clamp, cross-budget, layout-projection, and recovery surfaces are
intentionally deferred to the dependency-closed safety follow-up; this slice
alone is not yet the final framing bridge or semantic verifier.

**Part A fixed complete alignment safety A (infrastructure only).**
The first safety slice for `FixedPairOriginAlignment` now exposes exact literal
final fields and the full origin-aligned tape layout, proves that the declared
clock is the strict first terminal time, proves absorbing exact post-clock
execution, bounds the complete head/write footprint through the clock, and
classifies all boundary clamps. In particular, the time-2 right move clamps
exactly when `B = 0`, and the sole left clamp occurs at source time `clock-3`.
Cross-budget synchronization, fixed-extent recovery, the explicit zero edge,
and the bundled complete phase contract remain in Safety B.

**Part A fixed complete alignment safety B (infrastructure only).**
The second safety slice for `FixedPairOriginAlignment` proves exact
cross-budget accounting: equal zero/nonzero budget classes agree from time zero,
and all budgets synchronize from time three through the clock in state, numeric
head, and equal-address tape values. It proves fixed-extent recovery of the query
and witness without claiming varying-split injectivity, exposes the exact
`n=m=B=0` edge, and bundles the complete predecessor handoff, endpoint,
first-terminal, footprint, inclusive blank boundary, and literal output contract.
Together with Safety A, the origin-alignment machine now has its full advertised
execution and safety surface; semantic evaluation and the final framing bridge
remain separate.

**Part A fixed trailing content-marker erasure (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedPairContentMarkerErase` is a closed
four-state machine that scans the origin-aligned nonblank block, locates its end
structurally via the following blank, validates and erases the trailing literal
marker, and accepts at exact clock `n+m+3`. The scan treats data zero and one
uniformly and never identifies a marker by Boolean value. The final tape is
physical headerless `query ++ witness` at the origin with every allocated cell
from `n+m` onward blank. The phase proves exact full execution, strict first
terminal, absorption, no clamps, complete footprint, unconditional budget
independence, fixed-extent recovery, the empty zero-budget trace, and a bundled
contract containing `Fin.append`, post-clock, and budget clauses. It is not a
universal malformed-format validator and makes no varying-split injectivity
claim.

**Part A fixed content tag gate (infrastructure only).**
`Pnp3.Complexity.Uniform.V1.FixedContentTagGate` is a closed
15-state phase that rewinds the marker-erasure output in place, restores every
content bit, and checks the fixed eight-bit parser tag `10110010`. Its exact
common deadline is `3 * (n + m) + 7`; it proves each earlier malformed terminal,
no right clamp, the unique origin-detection left clamp, tape preservation,
blank-suffix preservation, and cross-budget equality. Its local accept is only
a handoff at header offset eight, not semantic acceptance. The pnp4
`FixedContentTagGateCorrect` bridge proves that every local rejection is sound
for both `contentSemanticAccepts` and `boundedContentSemanticAccepts`, including
the length-seven virtual-zero case where the padded tag itself matches but the
gamma header still fails. This begins concrete semantic activation; gamma
parsing, capped sizes, witness addressing, circuit decoding/evaluation,
phase composition, and V1-to-legacy simulation remain separate.

**Part A G1 fixed-content gamma terminator scan (infrastructure only).**
`FixedContentGammaTerminator` is a real three-state, nine-entry fixed-control
scan. Under a successful tag-gate handoff it receives the unchanged tape and
head at cell eight, accepts on the first physical `true`, rejects on the first
physical blank, never writes, and exposes exact first-terminal, tape, head,
absorption, and cross-budget contracts. Under that same successful-handoff
premise, `FixedContentGammaTerminatorCorrect` identifies the machine verdict
with `contentHeader?` presence and factors both semantic verifiers through the
header-presence predicate independently of machine execution.
This phase does not read the payload, materialize the decoded target, call
`computeContentSizesCapped`, check a cap, compose the phases, or claim capped
execution. Header presence is the cap-facing boundary for this slice.

**Part A G2a fixed-content gamma anchor (infrastructure only).**
`FixedContentGammaAnchor` is a six-state phase retagged from merged G1. On G1
success it walks left across the zero run, checks tag cells 6=true and 7=false,
erases exactly cell 7 as a recoverable marker, returns across the unchanged
zero run, and accepts on the same terminator at clock `2 * zeros + 5`. Its
common absorbing deadline is `2 * (n + m)`; G1-none rejects at the content
blank in one step. No payload traversal/value decoding, virtual payload read,
capped arithmetic, or semantic acceptance is claimed. G2b must not write
`none` in its counter zone and must restore cell 7 before a `contentTape` phase.

**Part A G2b fixed gamma-payload cursor core (infrastructure only).**
`FixedGammaPayloadCursorCore` is a 14-state, 42-entry fixed-control tracer
retagged from the exact successful G2a final configuration. It executes the
zero-width case with literal cell-7 restoration and exposes the first
rolling-hole read partition: physical false produces a canonical
`qNextFalse` handoff. Physical true and the first virtual blank now have exact
actual-run cleanup theorems at clock `3 * zeros + 6`; they finish at head 6 in
`qOne` and `qVirtual`, respectively, with literal `contentTape` restored.
`qOne` and `qVirtual` are absorbing internal outcome
tags; `machine.accept = qOne` is only this tracer's ABI choice, and `qVirtual`
is not a machine terminal. This slice does not prove arbitrary-round induction,
whole-payload traversal, `allZeroSlice?`
correctness, capped arithmetic, or semantic acceptance.

**Part A G2c fixed gamma-payload round step (infrastructure only).**
`FixedGammaPayloadRoundStep` is a new 11-state, 33-entry successor; it does not
change the core's published absorbing `qNextFalse` row.  Its machine-neutral
`roundTape` and machine-specific `RoundInvariant` describe every boundary
`1 ≤ k ≤ zeros`.  From a
reachable boundary with `k < zeros`, one physical-false round runs in exactly
`2 * zeros + 4` steps, restores the old payload hole, spends counter cell
`8 + k`, opens the next payload hole, and re-enters its own `qStart`.  A real
`k = 1 → 2` corollary starts from the core's `first_physical_false_exact`.
True, virtual, and exhausted branches are only explicit internal exit tags;
`machine.accept = qOnePending` is a local ABI choice, not a semantic-acceptance
claim.  No cleanup, whole-payload verdict, capped arithmetic, or semantic
claim is made. Boundary-only induction is provided by the G2d proof driver.

**Part A G2d fixed gamma-payload round driver (proof only; infrastructure only).**
`FixedGammaPayloadRoundDriver` proves that every boundary `1 ≤ k ≤ zeros`
is reachable when every absolute content cell
`9 + zeros ≤ j < 9 + zeros + k` is physically present and false. Its
transparent successor-local clock is `(k - 1) * (2 * zeros + 4)`: boundary one
is the real `startConfig` itself at local clock zero. This is not a
cross-machine total clock. The driver adds no exhausted, true, or virtual
outcome, no whole-payload verdict, and no semantic claim or bridge.

**Part A G2e fixed gamma-payload exhausted tail (proof only; infrastructure only).**
`FixedGammaPayloadExhausted` composes the last G2d boundary with the exact
successor-local tail `zeros + 3`, reaching the absorbing internal tag
`qExhausted` at head `8 + zeros` and leaving `roundTape` unchanged. Its clock
`boundaryClock zeros zeros + (zeros + 3)` is not a cross-machine total clock.
The proof uses `0 < zeros` and the full physically present false prefix,
establishes strict first arrival and no-clamp bounds, and performs no tape
restoration or cleanup. The tag does not claim a semantic all-zero verdict,
acceptance, or a complexity bridge.

**Part A G2h fixed gamma-payload pending outcomes (proof only; infrastructure only).**
`FixedGammaPayloadPendingOutcomes` composes every reachable boundary
`1 ≤ k < zeros` with an exact local round of cost `2 * zeros + 4`.  A physical
true at cell `9 + zeros + k` reaches absorbing `qOnePending`, while equality of
that cell with `a + m` reaches absorbing `qVirtualPending`; both stop on the
read cell with the same `pendingTape`, and both are strict first pending
outcomes.  The clock is successor-local.  This slice excludes `k = 0`,
`k = zeros`, cleanup, a whole-payload or semantic verdict, and any
cross-machine clock or complexity bridge.

**Part A G2f fixed gamma-payload physical zero cleanup (infrastructure only).**
`FixedGammaPayloadZeroCleanup` is a new five-state successor that retags the
exact G2e `qExhausted` endpoint without changing that absorbing predecessor
row. It scans right across the complete physical-false payload, fills the
cursor with literal `false`, returns across the payload and terminator, fills
the contiguous counter/anchor holes through cell 7, and stops on fixed tag
cell 6 in absorbing internal `qDone`. Its exact successor-local clock is
`3 * zeros + 3` for `0 < zeros`, with strict first arrival, head 6, and literal
`contentTape` restoration. The table has 15 rows and is independent of tape
budget; the proof also exposes its initial footprint and the exact arithmetic
bounds used to type its phase configurations. No run-level no-clamp theorem is
claimed. This is not
a semantic all-zero or acceptance result, and its clock is not combined with
any predecessor-machine time.

**Part A G2i fixed gamma-payload pending cleanup (infrastructure only).**
`FixedGammaPayloadPendingCleanup` is an eight-state successor of both exact G2h
pending endpoints for `1 ≤ k < zeros`. One retagged `qStart` reads the pending
cell: physical true selects `qBackOne`, the virtual blank selects
`qBackVirtual`, and physical false rejects. Thus no proof becomes branch
advice. Each branch restores holes `8+k` through `7` with physical false and
stops at cell 6 in distinct absorbing `qOne` or `qVirtual`. The strict first
successor-local endpoint is `zeros + k + 4`, with literal `contentTape`; the
wrong tag is excluded throughout. All 24 rows/resources are pinned, no row
moves right, heads are nonincreasing, and cells above the initial head remain
fixed. This is structural infrastructure only: no semantic verdict,
dispatcher correctness, acceptance meaning, cross-machine clock, or
complexity bridge is claimed, and it is not P-vs-NP mainline work.

**Part A G2k fixed gamma-payload dispatcher (infrastructure only).**
`FixedGammaPayloadDispatcher` is a 28-state/84-row fixed routed block sum from
the actual G2a deadline endpoint. It preserves three absorbing outcomes:
`qAllZero`, distinct internal `qHasOne`, and shared malformed `qReject`; the
control/table contain no input, zero count, width, or proof data. This slice
activates exact executable malformed, zero-width, and `k=0` true/virtual paths,
including literal tape and case-specific head outcomes (7 for zero width, 6
after cleanup), endpoint absorption, and budget independence. Later round,
pending, and exhausted routes are table-wired but not covered by unified run
theorems, so this is not a whole-dispatcher semantic claim and not mainline.

**Part A G2g fixed gamma-payload zero semantic bridge (infrastructure only).**
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaPayloadZeroSemanticBridge`
characterizes `VirtualZeroTailReader.allZeroSlice? = some true`, under exact
logical fit, by false blank-padded reads. With explicit physical and logical
fit it specializes this to the gamma payload window
`[9 + zeros, 9 + 2 * zeros)`, and combines the existing G2f endpoint with the
result at logical length `a + m`; the physical-false prefix itself proves that
fit. This is a one-way consequence of the existing `htag`/`hg`/`hzero`/full
physical-false hypotheses. It is not a `qDone` equivalence, semantic acceptance,
dispatcher correctness, complete parser correctness, or P-vs-NP mainline
progress.

**Part A G2j cleaned pending strict-reader semantics (infrastructure only).**
`ContentFixedGammaPayloadPendingSemanticBridge` freezes the strict-reader
boundary: for positive width, `allZeroSlice? = none` exactly when the logical
window does not fit, while under fit `some false` exactly means that some
`padRead` in the window is true.  It conjoins the G2i `qOne` and `qVirtual`
cleanup endpoints with their respective `some false` and `some true` scans for
arbitrary `T` satisfying `9 + 2 * zeros ≤ T`.  The virtual scan is exactly
`none` at physical `T = a + m`.  Both pending branches, and the small G2g zero
branch, also have corollaries at the shared frozen window `2 * (a + m) + 1`.
The payload remains exactly `[9 + zeros, 9 + 2 * zeros)`.  These are one-way
parallel consequences only, with no endpoint iff semantics, dispatch, parser,
decode, acceptance, cross-machine clock, or P-vs-NP mainline claim.

**P1b-0 fixed-width DAG-bundle composition (infrastructure only).**
`Complexity.DagBundleCompose` layers a fixed-output `DagBundle` over one shared
predecessor bundle with exact gate count `B.gates + S.gates`, and iteration from
the zero-gate identity has exact count `t * S.gates` and `Nat.iterate`
semantics.  `Complexity.DagGadgets` adds the small direct projection, constant,
NOT, AND, OR, and MUX surface.  See `pnp3/Docs/DagBundleCompose.md`.  This slice
does not provide a UniformTM configuration/step/run compiler, a polynomial-size
theorem, a `PpolyDAG` bridge, or a complexity-class rebind; it is not P-vs-NP
mainline progress.

**P1b-1 direct Uniform V1 configuration encoding (infrastructure only).**
`Complexity.Uniform.V1.CircuitEncoding` fixes the state/head/presence/value
layout with exhaustive block coverage, canonical three-symbol tape rails,
exact concrete encoding, and a two-shared-gate `initialBundle` with zero-gate
input projections.  Its length-one capstone separates a present false input
bit from blank padding.  The module reaches canonical `Complexity.Interfaces`
through the DAG gadgets; that interface transitively imports legacy
`PsubsetPpolyInternal.TuringEncoding`.  The P1b-1 construction and proofs use
neither that legacy TM nor its `runTime`, simulator/compiler, or frozen
`TMVerifier` semantics.  This slice provides no transition/step or run
compiler, polynomial-size simulation theorem, `UniformP`/`PpolyDAG` bridge,
canonical class rebind, or P-vs-NP mainline progress.

**P1b-2 encoded one-step semantic kernel (infrastructure only).**
`Complexity.Uniform.V1.StepKernel` defines a pure Boolean `encodedStep` that is
exact on canonical configuration encodings, including public-step terminal
semantics, old-head writes, and real clamped head movement.  Iteration agrees
with `UniformTM.run`.  A caller-supplied `StepSpec S` yields an exact
`runBundle` with `2 + t*S.gates` gates, but this slice constructs no concrete
step/action bundle or `StepSpec` witness.  `DagGadgets.bigOrCircuit` supplies a
linear direct false-seeded list disjunction with exact `List.any` semantics and
exact size `2 + sum C.size`, including size two for the empty list.  This slice
proves no polynomial simulation, `PpolyDAG` bridge or rebind, and is not
P-vs-NP mainline progress.

**P1b-3 direct shared step bundle (infrastructure only).**
`Complexity.Uniform.V1.StepBundle` materializes scan, exact three-symbol
classification, symbol-major transition rows, and filtered public-`M.step`
action rails in one shared predecessor graph. A `15*T` old-head update layer
is substituted once, yielding `stepBundle`, `StepSpec`, and the explicit bound
`19*T + 16*Q + 13`. This does not prove polynomial size for a run family,
`UniformP ⊆ PpolyDAG`, a canonical rebind, or P-vs-NP mainline progress.

**Final P1b versioned UniformP bridge (infrastructure only).**
`Complexity.Uniform.V1.PpolyDAG` builds the clocked run circuit solely from a
fixed `UniformTM`, clock exponent, and input length.  Its exact size is the
initial three units plus the clock times the direct step-bundle gate count, and
the all-input polynomial theorem uses the explicit exponent
`3 + (c+1)*(19*c + 16*M.stateCount + 70)`, with separate zero/one-length
proofs.  The completed endpoint is
`uniformP_subset_PpolyDAG : ∀ L, UniformP L → PpolyDAG L`, where `UniformP` is
only the versioned V1 class and `PpolyDAG` is the canonical DAG target.  P1c
separately proves countability and the length-only diagonal for that versioned
class. Neither slice rebinds or proves an equivalence for canonical `P`,
defines `UniformNP`, or proves a lower bound; neither is P-vs-NP mainline
progress.

Authoritative checklist:
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release posture:
`RELEASE_RC.md`.
Route policy lock:
`pnp3/Docs/CLOSURE_ROUTE_POLICY.md`.
Simulation fine-grained boundary:
`pnp3/Docs/Simulation_FineGrained_Status.md`.
Research method boundary:
`pnp3/Docs/Research_Method_Boundary.md`.

## Verified State

- Active `axiom` declarations in `pnp3/`: `0`.
- Active `sorry/admit` in `pnp3/`: `0`.
- `./scripts/check.sh` passes on the current tree (strict policy:
  no `sorry`/`admit` anywhere, no `sorryAx` in any term).
- Inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- That inclusion theorem is coarse polynomial-size DAG inclusion only; it is
  not a fine-grained Cook-Levin or hardness-magnification compiler adequacy
  theorem.
- The repository contains substantial DAG endpoint plumbing, including the
  fixed-slice DAG-to-formula bridge
  `Complexity.ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`.
- The former fixed-slice pnp3 AC0 endpoint is quarantined in
  `pnp3/LowerBounds/AC0_GapMCSP.lean`. Its standard-looking names are
  deprecated: `SmallAC0Solver_Partial` contains `params` and an enriched
  `easyData` payload that already imply `False` without solver correctness.
  The proved statement is only enriched-package inconsistency, not a standard
  AC0 lower bound and not P-vs-NP mainline progress.

## Current Audit Result

There is still **no unconditional in-repo theorem** `P != NP`, and the
current blockers are sharper than the old "remove residual payload" wording.

**Repository `P` runtime-advice caveat.**  The exact-step machine model described
under "Runtime model caveat on input (2)" below has a `P`-side consequence too:
since `runTime : Nat -> Nat` is unrestricted data, the `P` predicate bounds it
pointwise but never requires it to be computable or time constructible.
`lengthAdviceLanguage_in_repo_P`
(`pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean`) therefore proves
that every `A : Nat -> Bool`, with no computability hypothesis, yields a
length-only language in the current repository `P`, using a two-state machine
whose zero-or-one-step runtime stores `A n`.  The definition thus admits
arbitrary length languages, including languages obtained from noncomputable
sequences.  The theorem does not itself construct a noncomputable sequence or
formalize undecidability or a cardinality separation.

**Category: Infrastructure.** This is an interface audit, not a repair of the
model or P-vs-NP mainline progress.

The active public DAG endpoint is now the honest research-gap boundary:

```text
NP_not_subset_PpolyDAG_final
  (gap : ResearchGapWitness)

P_ne_NP_final
  (gap : ResearchGapWitness)
```

The legacy `hMS`/provider/support-bounds endpoints still compile, but they are
explicitly audit routes in `Magnification.FinalResultAuditRoutes`, not the
public closure boundary.  The falsifiability audit proves:

- `FormulaSupportRestrictionBoundsPartial -> False`
- `FormulaSupportBoundsFromMultiSwitchingContract -> False`
- `MagnificationAssumptions -> False`
- `FormulaSupportBoundsPartial_fromPipeline -> False`
- `MagnificationAssumptions_fromPipeline -> False`
- `FormulaCertificateProviderPartial -> False` (Probe 13, PR 13 audit)

So the legacy support-bounds, multi-switching, and certificate-provider
final routes are vacuous: they compile, but they route through inconsistent
assumptions.

**Note on PR #1366 canonical asymptotic infrastructure.**  PR #1366 landed
`canonicalAsymptoticHAsym` (unconditional fill of the
`AsymptoticFormulaTrackHypothesis` data structure) and a 7-session
TM-verifier construction plan for the canonical spec.  Probe 13 above shows
that the downstream wiring `i4_final_wiring_of_formulaCertificate` (the
consumer of a hypothetical `canonicalAsymptoticNPBridge_of_TM W`) is
ex-falso via `FormulaCertificateProviderPartial -> False`.  Therefore:

- The canonical infrastructure (slice-equality bridge, computable decider,
  TM-verifier scaffold) is sound Lean engineering and can be retargeted.
- The 7-session TM-verifier construction targeting `canonicalAsymptoticSpec`
  is **NOT** a path to unconditional `NP ⊄ P/poly` in the current
  formalization.  A future TM-witness consumer must route through a NEW
  provider that does not universally quantify over `PpolyFormula` (so it
  is not satisfied by truth-table hardwiring).

**Note on post-PR13 retarget chain (May 2026).**  The post-PR13 audit chain
landed three D0 / L0 deliverables under `seed_packs/`:

1. `seed_packs/post_pr13_provider_retarget_D0` (opus47):
   `RETARGET_EXISTING_ROUTE` — identified
   `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
   `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` as the
   two non-refuted DAG-side consumers of the canonical track.
2. `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55, PR #1378):
   `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS` — confirmed neither
   route imports `FormulaCertificateProviderPartial` or universally
   quantifies over `PpolyFormula`, and that NOGO-000004/6/8/9 do not
   transfer.
3. `seed_packs/hInDag_triviality_probe_D0` (gpt55, PR #1383):
   `YELLOW_INCONCLUSIVE` — no markdown-only argument settles the
   triviality question; blocking construction is either
   `canonicalAsymptotic_in_P` (multi-session TM-verifier plan) OR a
   direct DAG truth-table hardwiring at fixed slice.
4. `seed_packs/hInDag_triviality_probe_L0` (gpt55, PR #1388):
   `RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN` — the L0-A route closed.
   `pnp3/Tests/HInDagTrivialityProbe.lean` (121 LOC, kernel-checked,
   no `axiom`/`opaque`/`sorry`/`native_decide`, no refuted-predicate
   imports) defines:

   ```lean
   noncomputable def fixedSlice_gapPartialMCSP_in_PpolyDAG
       (p : GapPartialMCSPParams) : InPpolyDAG (gapPartialMCSP_Language p)

   noncomputable def hInDag_for_canonicalAsymptoticHAsym :
       ∀ n β, InPpolyDAG (gapPartialMCSP_Language
         ((eventualGapSliceFamily_of_asymptotic
             canonicalAsymptoticHAsym).paramsOf n β))
   ```

   via per-slice truth-table DAG hardwiring at the single encoded length
   `partialInputLen p` plus `constFalseDag` elsewhere.  The polynomial
   bound holds with a slice-dependent constant `K_p` because
   `InPpolyDAG.polyBound_poly` requires polynomiality in the input
   length `n`, and constant-in-`n` is polynomial.

**Structural consequence of the L0 landing.**  Both
`AsymptoticIsoStrongRoute canonicalAsymptoticHAsym` and
`AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym` have
the shape `∀ hInDag, <structural conclusion>`.  With
`hInDag_for_canonicalAsymptoticHAsym` now Lean-witnessed, the `∀`
collapses to instantiation at the hardwired witness.  But the derived
`ppolyDAGSizeBoundOnSlicesEventually F hInDag` under truth-table
`polyBound = K_p` is a per-slice constant of order `2^N` at canonical
input length `N = 2 · 2^m`, doubly-exponential in the slice index.
"Small DAG" under this bound admits essentially every DAG of size
`≤ 2^N`, so the iso-strong / promise-YES conclusions now ask for
YES-isolating combinatorial structure for **arbitrary-size DAGs**, not
just polynomial-size DAGs.

**Note on canonical asymptotic track conclusion-side refutation
(May 2026, completed).**  Following the L0 hInDag triviality
landing, the audit chain continued with three additional D0 and L0
deliverables that ultimately **refuted the canonical track at the
conclusion level**:

5. `seed_packs/global_hInDag_contract_repair_D0` (codex53, PR #1396):
   `REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS` — proposed
   `GlobalAsymptoticDAGWitness` structure with single shared
   `(coeff, exponent)` polynomial bound to structurally close the
   hardwiring loophole.
6. `seed_packs/global_hInDag_contract_L0` (gpt55, PR #1404):
   `RED_GLOBAL_CONTRACT_CORE_LANDED` — landed
   `pnp3/Tests/GlobalHInDagContractProbe.lean` (116 LOC) with
   `GlobalAsymptoticDAGWitness` + `globalPolyDAGSizeBound` +
   `AsymptoticPromiseYesWeakRouteEventually_global` +
   `globalWitness_to_hInDag` forward projection.  Hypothesis-side
   hardwiring loophole structurally closed.
7. `seed_packs/isoStrong_conclusion_audit_D0` (codex53, PR #1407):
   `INCONCLUSIVE_NEEDS_LEAN_PROBE` — 4/4 D0 workers identified the
   conclusion-side question needs Lean probe.
8. `seed_packs/isoStrong_conclusion_L0` (codex, PR #1413):
   `YELLOW_PARTIAL_LANDING` — landed
   `pnp3/Tests/IsoStrongConclusionProbe.lean` (80 LOC; now archived under
   `archive/pnp3/Tests/`, subsumed by stage 14) with `F_Mof =
   n+2` simp lemma + `canonical_isoStrong_implies_eventual_strict_slack`
   slack-inequality extraction.  Identified pigeonhole
   z-construction as L1 blocker.
9. `seed_packs/isoStrong_conclusion_L1` (4 codex sessions, PRs
   #1416, #1423, #1427, #1433):
   **`RED_CONCLUSION_REFUTED`** — the canonical iso-strong route is
   **formally inconsistent** at canonical `sYES=1, sNO=2`.  Total
   staging file size: 409 LOC, kernel-checked, no `axiom`/`opaque`/
   `sorry`/`admit`/`native_decide`, no refuted-predicate imports.

The L1 chain (4 sessions) proved the **fourth major refutation** in
the post-PR13 chain via a corrected pigeonhole argument over
size-1 candidate traces on truth-table rows:

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

**Proof structure:**
1. Pigeonhole core (session 1): `Size1Candidate n` finite type with
   `Fintype.card = n + 2`; `exists_trace_not_size1_of_card_lt` shows
   that under slack `n + 2 < 2 ^ Fintype.card α`, there exists a
   Boolean labeling outside all size-1 traces.
2. Encoding bridge (session 2): `traceSize1CandidateOnRows` evaluates
   size-1 candidates on truth-table rows via `Nat.testBit`;
   `diagonalPartialTable` constructs the candidate counterexample
   `z := encodePartial (diagonalPartialTable p yYes D label)`;
   `diagonal_z_valid` (ValidEncoding) and `diagonal_z_agrees_on_D`
   (AgreeOnValues) verify two of the three required properties.
3. Not-YES bridge + composition (session 3):
   `is_consistent_diagonal_table_implies_label_trace` (size-1
   consistency → label equals trace);
   `diagonal_z_not_yes_of_label_not_trace` (contradiction with
   label-not-in-trace hypothesis);
   `exists_valid_agreeing_not_yes_under_slack` (full composition).
4. Main theorem assembly (session 4):
   `correctOnPromiseSlice_of_InPpolyDAG_family` (lift InPpolyDAG to
   CorrectOnPromiseSlice); `slack_for_D_of_isoStrong_slack` (convert
   iso-strong slack κ-form to D.card-form); compose with `hForce`
   and `exists_valid_agreeing_not_yes_under_slack` to derive
   contradiction.

**Consequence.** The canonical asymptotic track via
`canonicalAsymptoticHAsym` is closed at conclusion level in the
following precise sense:

- The iso-strong route is formally refuted.  The in-build kernel-checked
  witness is the general theorem `isoStrong_conclusion_negative_general`
  (`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, stage 14 below), which
  subsumes the canonical instance `isoStrong_conclusion_negative_for_canonical`.
  The original canonical-specific staging probe
  (`IsoStrongConclusionProbe.lean`, stages 9–11) has been archived to
  `archive/pnp3/Tests/` now that the general theorem covers it.
- The promise-YES weak and promise-YES certificate routes are now also
  exposed as standalone Lean negation theorems in
  `pnp3/Tests/PromiseRouteConclusionProbe.lean`:
  - `promiseYesCertificate_conclusion_negative_for_canonical` and
  - `promiseYesWeak_conclusion_negative_for_canonical`,
  each with the same `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym, ¬ ...`
  shape as the iso-strong companion.  They are corollaries of the
  iso-strong negation composed with the pointwise versions of the
  existing route-level implications
  `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`
  (`pnp3/Magnification/FinalResultMainline.lean:348`) and
  `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`
  (`pnp3/Magnification/FinalResultMainline.lean:400`).
- This makes the audit chain self-contained in Lean: instead of the
  closure of the certificate / weak routes living in the prose paragraph
  above, the closure is now three theorems with the same shape.
- Inhabitancy caveat: `GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym`
  is referenced only as a universal hypothesis (`∀ W : ...`) in the
  inspected files; no explicit inhabitant is constructed in the current
  codebase.  This is recorded as context; the `∀ W, ¬P(W)` theorem is
  logically meaningful as-is.

This does **NOT** prove `P ≠ NP` or even `NP ⊄ P/poly`.  It rules
out the canonical asymptotic track at the canonical `sYES = 1,
sNO = 2` spec as a route to those endpoints.  Future P-vs-NP mainline
work must pivot to a different route family:

- pnp4 frontier `SearchMCSPWeakLowerBound` /
  `VerifiedNPDAGLowerBoundSource`;
- or genuinely new research-level mathematics proving
  `ResearchGapWitness` directly.

The deprecated
`pnp3/LowerBounds/AC0_GapMCSP.lean::gapPartialMCSP_not_in_AC0` name is
only a compatibility alias for enriched-package inconsistency. The canonical
certificate `false_of_smallAC0Params_and_easyFamilyData` uses the parameter
capacity bound, AC0 realizability of the packaged family, and its
all-functions-scale cardinality lower bound; it does not use solver
correctness. It is not a standard AC0 exclusion.

A new canonical spec with non-trivial `sYES/sNO`, where the pigeonhole
argument does not apply (i.e., `Mof` grows fast
enough relative to `tableLen` to invalidate the slack inequality
used in `slack_for_D_of_isoStrong_slack`) is also an internal
spec-engineering option, not a publishable route on its own.

**Audit chain summary (16 stages, all kernel-checked).**

| Stage | Verdict | Lean witness |
|---|---|---|
| 1. PR 13 / Probe 13 | `FormulaCertificateProviderPartial → False` | `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` |
| 2. post_pr13_provider_retarget_D0 (opus47) | RETARGET_EXISTING_ROUTE | markdown audit |
| 3. asymptotic_isostrong_route_audit_D0 (gpt55, #1378) | YELLOW | markdown audit |
| 4. hInDag_triviality_probe_D0 (gpt55, #1383) | YELLOW_INCONCLUSIVE | markdown audit |
| 5. hInDag_triviality_probe_L0 (gpt55, #1388) | RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN | `HInDagTrivialityProbe.lean` (121 LOC) |
| 6. global_hInDag_contract_repair_D0 (codex53, #1396) | REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS | markdown audit |
| 7. global_hInDag_contract_L0 (gpt55, #1404) | RED_GLOBAL_CONTRACT_CORE_LANDED | `GlobalHInDagContractProbe.lean` (116 LOC) |
| 8. isoStrong_conclusion_audit_D0 (codex53, #1407) | INCONCLUSIVE_NEEDS_LEAN_PROBE | markdown audit |
| 9. isoStrong_conclusion_L0 (codex, #1413) | YELLOW_PARTIAL_LANDING | `IsoStrongConclusionProbe.lean` (80 LOC; staging probe now archived under `archive/pnp3/Tests/`, subsumed by stage 14) |
| 10. isoStrong_conclusion_L1 sessions 1-3 (#1416, #1423, #1427) | YELLOW_PARTIAL chain | extends to 340 LOC |
| 11. isoStrong_conclusion_L1 session 4 (#1433) | **RED_CONCLUSION_REFUTED** | extends to 409 LOC; `isoStrong_conclusion_negative_for_canonical` formally proved (staging probe now archived; subsumed by stage 14's general theorem) |
| 12. general_isoStrong_no_go D0 (codex53, ffd47f6) | NEEDS_LEAN_PROBE | markdown audit |
| 13. circuit_count_trace_bound L0 (codex53, c436392) | GREEN_COUNTING_BRICKS_LANDED | `CircuitCountTraceBoundProbe.lean` (~120 LOC) |
| 14. general_isoStrong_no_go L1 sessions 1-4 (codex53+opus47, 75c5ae0 → 24d51510) | **RED_GENERAL_ISOSTRONG_REFUTED** | `GeneralIsoStrongNoGoProbe.lean` (~460 LOC); `isoStrong_conclusion_negative_general` formally proved over arbitrary `GapSliceFamilyEventually` |
| 15. general_isoStrong_route_closure (opus47) | **ROUTES_NAMED_AS_CLOSED** | `GeneralIsoStrongRouteClosure.lean` (~120 LOC); four named route-closure theorems |
| 16. promise_route_conclusion_companions | **CONCLUSION_COMPANIONS_NAMED** | `PromiseRouteConclusionProbe.lean`; `promiseYesCertificate_conclusion_negative_for_canonical` and `promiseYesWeak_conclusion_negative_for_canonical` standalone theorems with the same `∀ W, ¬ ...` shape as `isoStrong_conclusion_negative_for_canonical` |

The canonical asymptotic track is now closed at conclusion side via
standalone Lean theorems (iso-strong via the in-build general theorem
`isoStrong_conclusion_negative_general`, which subsumes the archived
canonical `isoStrong_conclusion_negative_for_canonical`; promise-YES
certificate and promise-YES weak via the two companions in
`PromiseRouteConclusionProbe.lean`).  The
four major refutations in the post-PR13 chain:

1. `FormulaCertificateProviderPartial → False` (PR 13, formula-side
   truth-table hardwiring).
2. `hInDag_for_canonicalAsymptoticHAsym` provable
   (L0 #1388, DAG-side per-slice truth-table hardwiring).
3. Global contract structurally closes hypothesis side
   (L0 #1404).
4. **`isoStrong_conclusion_negative_for_canonical` provable
   (L1 sessions 1-4, canonical track formally inconsistent at
   conclusion level).**

**Note on general iso-strong refutation and route-level closure
(May 2026, completed).**  Following the canonical L1 session 4
landing, the audit chain continued with a D0 audit, an L0 counting-
brick probe, and four L1 sessions that lifted the canonical
refutation to the general `GapSliceFamilyEventually` schema.  After
these steps the route-level refutation lives in
`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean` as

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag
```

and the strategic consequence is packaged as four named theorems
in `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`:

- `not_AsymptoticIsoStrongRoute_of_hInDag`
  (parameter-agnostic helper);
- `not_AsymptoticIsoStrongRoute_canonical`
  (instantiated via `HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`);
- `not_AsymptoticPromiseYesCertificateRoute_canonical`
  (via `asymptoticIsoStrongRoute_of_asymptoticPromiseYesCertificateRoute`);
- `not_AsymptoticPromiseYesWeakRouteEventually_canonical`
  (via `asymptoticPromiseYesCertificateRoute_of_asymptoticPromiseYesWeakRouteEventually`).

All four are kernel-checked with standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`).  They make the iso-strong /
promise-YES certificate / promise-YES weak route class **formally
retired** at the canonical asymptotic instantiation: each named
theorem refutes the corresponding route prop directly, so a future
reader scanning the route catalogue can identify these three routes
as closed without re-deriving the meta-argument.

This does **NOT** prove `P ≠ NP` or `NP ⊄ P/poly`.  It closes the
iso-strong route class as a path to those endpoints; future
P-vs-NP mainline work must pivot to a different route family —
either the pnp4 frontier (`SearchMCSPWeakLowerBound` /
`VerifiedNPDAGLowerBoundSource`) or genuinely new research-level
mathematics proving `ResearchGapWitness`. The deprecated
`gapPartialMCSP_not_in_AC0` compatibility theorem proves only that an
inconsistent enriched easy-family package cannot exist; it is neither an AC0
lower bound nor a closure route.

## Fixed-Params Status

Session 67 introduced the stronger contract
`FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb`.

Session 68 established the current honest boundary:

- the Probe 7 singleton-provider attack does not directly port to fixed
  external `ac0` parameters;
- `fixedParams ac0 sb` alone is not currently refuted in the project;
- `fixedParams ac0 sb` plus uniform provenance for every formula witness under
  the same `ac0` reconstructs the old false support-bounds predicate;
- therefore the pair `fixedParams + uniformProvenance` is formally
  inconsistent in the current formalization.

The theorem
`NP_not_subset_PpolyDAG_final_under_fixedParams_and_uniformProvenance`
is useful as a gap-exposing theorem, not as progress toward an unconditional
claim.  Its assumptions describe the research-level hole.

The single-file boundary for future closure is
`pnp3/Magnification/UnconditionalResearchGap.lean`.  It contains
`ResearchGapWitness` and the compiled bridge
`P_ne_NP_of_researchGap : ResearchGapWitness -> P_ne_NP`; a future
unconditional proof should be localized there by proving
`ComplexityInterfaces.NP_not_subset_PpolyDAG` without using the refuted
support-bounds surfaces.

`ResearchGapWitness` is method-agnostic.  AC0/locality/restriction/shrinkage
routes, including `AcceptedFamilyCertificateAt`, are optional sufficient
routes and compatibility surfaces, not the required format for a future
algebraic, spectral, finite-field, SOS, or other non-combinatorial proof.

## What Is Closed

### Canonical asymptotic track (May 2026)

The asymptotic anti-checker pair `(hAsym, hNPbridge)` is no longer a
hypothesis parameter throughout the magnification mainline.  See
`pnp3/Magnification/CanonicalAsymptoticTrackData.lean`:

- `canonicalAsymptoticSpec : GapPartialMCSPAsymptoticSpec` — minimal legal
  asymptotic spec (`sYES = 1, sNO = 2`); all four structure fields built.
- `canonicalAsymptoticParams n hn : GapPartialMCSPParams` — per-slice
  parameters at slice `n ≥ 8` with Shannon-counting `circuit_bound_ok`
  proved unconditionally via `canonicalShannonBound`.
- `canonicalSliceEq : ∀ n hn x, asymp(...) = perSlice(...)` — Lean
  technical bridge for the `Classical.choose` dependent cast.  Closed via
  an `Eq.rec` motive parameterised over the type-level witness proof; the
  base case reduces the cast through `Subsingleton.elim` on the `Eq`
  proof.  The supporting helper
  `Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen` is in
  `Model_PartialMCSP.lean`.
- `canonicalAsymptoticHAsym : AsymptoticFormulaTrackHypothesis` —
  **unconditional**.
- `canonicalAsymptoticNPBridge_of_TM W`, `canonicalAsymptoticData_of_TM W`,
  `canonicalAntiCheckerAssumptions_of_TM W` — produce the strict NP
  package from a single concrete TM-verifier witness
  `W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

`pnp3/Tests/CanonicalIntegrationTests.lean` validates end-to-end
integration wiring surfaces, including
`i4_final_wiring_of_formulaCertificate` and
`NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`.
The canonical conclusion-side closure is witnessed in-build by the general
iso-strong theorem `isoStrong_conclusion_negative_general`
(`pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`) together with the two canonical
promise companions `promiseYesCertificate_conclusion_negative_for_canonical` /
`promiseYesWeak_conclusion_negative_for_canonical`
(`pnp3/Tests/PromiseRouteConclusionProbe.lean`).  The canonical-specific
iso-strong staging probe (`isoStrong_conclusion_negative_for_canonical`,
`IsoStrongConclusionProbe.lean`) is archived under `archive/pnp3/Tests/` and is
subsumed by the general theorem.

The historical remaining typed deliverable for that independent infrastructure
milestone was the TM verifier. Its implementation plan is now frozen; the
retained details under "What Is Still Open" are an archival record, not the
active engineering queue.

### Inclusion side

- Default inclusion is internalized via
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- Default final wrappers no longer need external inclusion-contract bundles.
- The simulation layer is closed only at the coarse `P_subset_PpolyDAG` level:
  its active size contract is existential polynomial (`n^k + k`), not a
  fine-grained overhead bound.  This is sufficient for
  `ResearchGapWitness -> P_ne_NP_final`, but not for any future route that
  depends on exact magnification slack.

### DAG plumbing

- The fixed-slice DAG-to-formula bridge exists.
- Route-B, source-closure, blocker, asymptotic, and `_TM` endpoint wrappers are
  implemented.
- This plumbing is useful for future magnification arguments.

### Fixed-slice no-go status

The historical fixed-slice support-half route is a closed no-go branch under
fixed-slice `PpolyDAG` membership:

- `no_fixedSlice_stableRestriction_of_inPpolyDAG`
- `no_fixedSlice_blocker_of_inPpolyDAG`
- `not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG`

## What Is Still Open

### Canonical-track TM-verifier deliverable (frozen historical roadmap)

> **Freeze note.** This roadmap is paused; the tree snapshot is pinned at Git
> tree `b49456d6`, the subtree of commit `7b53a08f` (two migrations since
> `42c59881`: the reviewed S11 acceptance closure and the single authorized
> GN-E2-3b body-driver slice, neither of which resumed the roadmap). The
> active engineering queue is the versioned uniform complexity foundation
> outside TMVerifier.

> **Scope note.**  After the canonical iso-strong / promise-YES
> conclusion-side refutations recorded above, the canonical asymptotic
> track is **no longer a P-vs-NP closure route**.  The TM-verifier
> deliverable below is therefore an independent formalization /
> infrastructure milestone for the reusable NP-verifier and decider
> scaffolding.  Finishing it does not reduce the `ResearchGapWitness`
> gap by itself, and it must not be presented as P-vs-NP progress.

Considered as an isolated infrastructure target, the canonical
asymptotic infrastructure reduces to a single typed object:

```
W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec
```

i.e., a concrete polynomial-time TM that verifies
`gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec` against a
size-1 circuit certificate.  Mathematically this is the published
OPS19/CJW20 fact `GapMCSP ∈ NP` (one-half-page argument in textbooks).

**Decomposition (May 2026)**:
`pnp3/Magnification/CanonicalAsymptoticDecider.lean` reduces the
obligation to a single TM-engineering target.  It contains:

- `decideAsymptotic : (n : Nat) → Bitstring n → Bool` — a computable
  decider equal pointwise to `gapPartialMCSP_AsymptoticLanguage
  canonicalAsymptoticSpec` (proved as `decideAsymptotic_iff`).
- `findCanonicalSlice` — fully axiom-free `Option Nat` detector for
  canonical input lengths `Partial.inputLen m = 2 · 2^m`.
- `decideYesAt1` — enumerates the `m + 2` size-1 circuit candidates
  and checks consistency via the now-proved `is_consistent_iff_bool`.
- `CanonicalAsymptoticVerifierComponents` — the minimum-sufficient
  structure: a TM `M` plus the property `accepts (x ++ w) = decideAsymptotic n x`
  for every certificate `w`, plus the polynomial-runtime bound.
- `witnessOfComponents : Components → GapPartialMCSP_Asymptotic_TMWitness
  canonicalAsymptoticSpec` — closed bridge.

After this decomposition, the only remaining sub-obligation **for the
infrastructure milestone** is to construct a TM whose acceptance
behaviour matches the (now-defined) `decideAsymptotic` function, with
polynomial runtime.  All decidability and language correctness are
closed; the engineering reduces to "build a TM that ignores `w` and
computes a known Bool function on `x`".  Again, this is reusable
NP-verifier infrastructure, not a P-vs-NP closure step.

**Multi-session plan**: see `pnp3/Docs/TMVerifier_Session_Plan.md` for
the 7-session decomposition (Variant B NP-style architecture):

1. Session 1: `seqList_run_full` (generic CS-composition correctness)
2. Session 2: `writeVecOfNatProgram` + `_run_full`
3. Session 3: `mcspCheckAllRows_correct`
4. Session 4: Witness decoder (`decodeCandidateSpec` + `_writeToTape_run_full`)
5. Session 5: `canonicalLengthCheckProgram_run_full`
6. Session 6: Top-level composition `verifierProgram_accepts_iff`
7. Session 7: Runtime bound + final `canonicalAsymptoticVerifierComponents` term

Each session = ~350 LOC, closes one leaf theorem with 0 sorry / standard
classical axioms.  Total estimated work: ~2500 LOC over 7 sessions.

### Research-gap source theorem (longer-horizon)

The remaining blocker is not endpoint plumbing.  It is the missing
non-vacuous source theorem for `ResearchGapWitness`, equivalently
`ComplexityInterfaces.NP_not_subset_PpolyDAG`.

A real lower-level route may still come from support/locality mathematics, but
only if it produces DAG separation through a provenance gate that:

1. does not quantify over arbitrary `PpolyFormula` witnesses;
2. cannot be satisfied by truth-table hardwiring or singleton provenance;
3. uses fixed, externally meaningful AC0 parameters;
4. does not combine with an overbroad uniform-provenance assumption to imply
   the old false support-bounds predicate.

That missing theorem is the research-level mathematical gap.  It should be
treated as open, not as a Lean engineering task.

Green CI and a passing `./scripts/check.sh` are formal hygiene checks, not
mathematical progress toward `NP_not_subset_PpolyDAG` by themselves.  They
prevent stale or vacuous route claims from re-entering the tree; they do not
replace the missing lower-bound idea.

### pnp4 conditional decision→search extraction chain (June 2026)

`pnp4/Pnp4/Frontier/ContractExpansion/` now formalizes a verified **conditional**
chain that replaces the abstract
`SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource` jump with explicit,
machine-checked interfaces: from a `PpolyDAG` membership of the prefix-extension
language it extracts a bounded search solver, and contrapositively
`NoPolynomialBoundedSearchSolver + growth ⇒ ¬ PpolyDAG`; combined with an
NP-membership witness it assembles a `VerifiedNPDAGLowerBoundSource`.

This is **not** unconditional progress: it proves neither `P ≠ NP` nor
`NP_not_subset_PpolyDAG`.  The codec/growth machinery is now concrete: the **first
concrete `TreeCircuitWitnessCodec`** is constructed (`ConcreteTreeCodec.lean`), and
`PolyBoundedInTable` is proved for the canonical polynomial thresholds
(`ThresholdGrowth.lean`).  So at a concrete polynomial threshold the original
consolidated theorem (`ConsolidatedTreeSeparation.lean`, `verifiedSource_treePoly` /
`NP_not_subset_PpolyDAG_treePoly`) has **exactly two** explicit open inputs:

1. `NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k))` — a
   genuine `P/poly` circuit lower bound for the concrete tree-MCSP search problem
   (the same research-level lower-bound gap described above);
2. `PrefixExtensionNPWitness (…)` — a concrete NP verifier (TM + runtime + certificate
   correctness).

The preferred verifier target is now the content-truthful reroute in
`ContentConsolidatedSource.lean`. Its concrete capstone
`NP_not_subset_PpolyDAG_treePolyCT` likewise has exactly two explicit hypotheses: the same
`NoPolynomialBoundedSearchSolver` and
`ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))`.

The post-GATE/I1/D1b boundary is exact. The convention-length equality gate and gamma narrowing are
proved; `contentInput?` retains exactly three tag/index/padding read-value tests; and concrete
`ContentAccepts` non-vacuity is proved. D1b is complete as a **conditional repackaging** from a
supplied `ContentVerifierBridge` to the content NP-witness interface. Still open are wrapper-level
`L'` padding invariance, an actual concrete verifier bridge (machine, runtime proof, and exact-step
acceptance equation), formal runtime/advice enforcement, and the
`NoPolynomialBoundedSearchSolver` lower bound. None of the closed specification or packaging work
constructs a bridge instance or proves NP membership.

**Runtime model caveat on input (2).**  `NP` there is `NP_TM`
(`pnp3/Complexity/Interfaces.lean`) over `Pnp3.Internal.PsubsetPpoly.TM`
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`): a deterministic
single-tape binary-alphabet machine with no separate read-only input tape and fixed tape
length `n + runTime n + 1` (`TM.tapeLength`), whose `runTime : ℕ → ℕ` is a **structure
field** rather than a derived step count, and whose `TM.accepts` is evaluated **at
exactly step `runTime n`** (`TM.run` iterates `stepConfig` exactly `M.runTime n` times,
then checks `state = M.accept`) with no halting predicate.  Because the declared budget
is also the evaluation point, the verifier interfaces' `runTime_poly` field is a genuine
restriction on the machine, not a self-certification.  That restriction is numeric
only — it bounds the size of `runTime` without constraining *which* function it is — and
the `P`-side consequence of that is the runtime-advice caveat recorded above.  No
cross-model runtime-robustness theorem is formalized, so input (2) is an obligation
*in this model*.
This is the NP-side analogue of the coarse-inclusion caveat recorded above for
`proved_P_subset_PpolyDAG_internal`.

**Honest caveat — one-way extraction, not an equivalence.**  The decision→search
extraction is formalized in **one direction only**:

```text
PpolyDAG (prefix-extension language) → polynomial-size bounded search solver
```

that is `boundedSearchSolver_of_PpolyDAG_prefixExtension`
(`pnp4/Pnp4/Frontier/ContractExpansion/BoundedSolverFromPpoly.lean`), together with its
contrapositive in two forms: the exact-schedule
`not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver`
(`ContractExpansion/NoSolverContrapositive.lean`, no growth premise) and the
polynomial-target `not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver`
(`ContractExpansion/ExtractedScheduleGrowth.lean`, which adds
`TreeMCSPExtractionGrowthAssumptions` and is derived from the exact-schedule form).
Both restate the same single direction.  The converse
(solver ⇒ `PpolyDAG`) is **not** formalized: `ContractExpansion/` contains no `Iff`
between `PpolyDAG` and a solver and no `PpolyDAG_of_boundedSearchSolver` declaration.

Since the instance length is `tableLen n = 2^n`, input (1) is therefore **at least as
strong as** the full `P/poly` lower bound "this concrete NP language is not in
`P/poly`" — and, absent the converse, possibly strictly stronger.  It is **not** a
weak/local bound amplified by hardness magnification, and no magnification theorem is
formalized: the chain makes the target precise and verified-conditional, not easier.
See `pnp4/Pnp4/Frontier/ContractExpansion/README.md` for the full module map and
proved-vs-open breakdown.

## Repository-Wide Honesty Policy

Any file claiming unconditional `P != NP` is inaccurate until the
project has either a non-vacuous replacement for the refuted
support-bounds / multi-switching source, or a direct method-agnostic
proof of `ResearchGapWitness` / `ComplexityInterfaces.NP_not_subset_PpolyDAG`
(algebraic, spectral, finite-field, SOS, Fourier-analytic, or other),
together with a zero-argument final theorem that does not depend on
external provider payload.
