import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.GuardedFiniteCachedAllBlocksInPlaceCompiler
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGToHSG

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One canonical aggregate: support-HSG and signed-WPRG endpoint

The accepting timed-alpha components form an unambiguous family, but
approximating every member separately loses the sum of the component errors.
This file instead forms their **single finite aggregate predicate** and proves
that it is exactly bounded deterministic one-tape acceptance.  Consequently:

* hitting this one aggregate is equivalent to the support-only HSG premise
  already consumed by the deterministic MCSP capstone; and
* a signed weighted approximation for this one aggregate, with error below
  one half, excludes an exact MCSP decider directly.

There is no union bound and no family of per-alpha approximation hypotheses in
these statements.  They do not construct the missing HSG/WPRG and do not show
that the aggregate itself belongs to a small read-once or circuit class.  The
master-guarded fused compiler realizes the unique accepting component; the
remaining aggregate-class/locality theorem is deliberately not assumed here.

Under the repository route policy this is a restricted lower-bound side
track: it does not reduce `SearchMCSPWeakLowerBound` or
`VerifiedNPDAGLowerBoundSource`, and supplies no `PpolyDAG` bridge.
-/

open StreamingMagnification
open StreamingMagnification.TotalSearch

local instance cachedInputMachineStateDecidableEqForCanonicalAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-! ## Exact-horizon and bounded acceptance -/

/-- Because terminal configurations stutter, acceptance by a finite horizon
is equivalent to acceptance of the configuration at that exact horizon. -/
theorem acceptsWithin_iff_accepting_run_at_horizon
    (machine : DeterministicMachine) (input : List Bool) (steps : Nat) :
    AcceptsWithin machine input steps <->
      IsAccepting machine (run machine input steps) := by
  constructor
  · rintro ⟨first, hfirst, haccept⟩
    obtain ⟨later, rfl⟩ := Nat.exists_eq_add_of_le hfirst
    have hhalt : machine.halt (run machine input first).state =
        some .accept := by
      simpa [IsAccepting, outcome] using haccept
    rw [run, runFrom_add_eq_runFrom_runFrom]
    change IsAccepting machine
      (runFrom machine input (run machine input first) later)
    rw [runFrom_eq_self_of_halted machine input
      (run machine input first) .accept hhalt]
    exact haccept
  · intro haccept
    exact ⟨steps, le_rfl, haccept⟩

/-! ## The single coherent timed-alpha aggregate -/

private theorem finset_fold_or_eq_true_iff
    {α : Type*} (items : Finset α) (predicate : α -> Bool) :
    items.fold (· || ·) false predicate = true <->
      exists item, item ∈ items /\ predicate item = true := by
  have h := Finset.fold_op_rel_iff_or
    (s := items) (op := fun left right : Bool => left || right)
    (b := false) (f := predicate)
    (r := fun _ value : Bool => value = true) (c := false) (by
      intro x y z
      simp)
  simpa using h

/-- Finite existential aggregate of all in-place accepting timed-alpha
components.  The ambient alpha type has a computable enumeration because
every deterministic machine carries its `stateFintype` as data.  This
Mathlib version has no `Finset.any`; the explicit `Finset.univ.fold` with
Boolean `or` below is exactly that operation.  It needs neither `Classical`
nor a `DecidableEq` instance for the full ambient alpha carrier. -/
def timedAlphaInPlaceAcceptingAggregateCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) : Bool := by
  letI : Fintype machine.State := machine.stateFintype
  exact Finset.univ.fold (· || ·) false fun alpha :
      AmbientTimedCanonicalAlpha machine.State T b =>
    timedAlphaInPlaceAcceptingComponentCheck machine input T b hb alpha

/-- The aggregate accepts exactly when one (necessarily unique) canonical
timed-alpha component accepts. -/
theorem timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff_exists
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    timedAlphaInPlaceAcceptingAggregateCheck machine input T b hb = true <->
      exists alpha : AmbientTimedCanonicalAlpha machine.State T b,
        timedAlphaInPlaceAcceptingComponentCheck
          machine input T b hb alpha = true := by
  letI : Fintype machine.State := machine.stateFintype
  unfold timedAlphaInPlaceAcceptingAggregateCheck
  rw [finset_fold_or_eq_true_iff]
  simp

/-- Exact semantic collapse of the coherent aggregate: it is one Boolean
presentation of deterministic acceptance at horizon `T`. -/
theorem timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    timedAlphaInPlaceAcceptingAggregateCheck machine input T b hb = true <->
      IsAccepting machine (run machine input T) := by
  rw [timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff_exists]
  exact exists_timedAlphaInPlaceAcceptingComponentCheck_iff
    machine input T b hb

/-- On truth tables, the single aggregate is pointwise identical to the
bounded-acceptance indicator used by the signed-WPRG/HSG capstone. -/
theorem timedAlphaInPlaceAcceptingAggregateCheck_eq_acceptanceIndicator
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n : Nat} (T b : Nat) (hb : 0 < b) (table : TruthTable n) :
    timedAlphaInPlaceAcceptingAggregateCheck
        machine (tableBits table) T b hb =
      deterministicTableAcceptanceIndicator machine T table := by
  apply Bool.eq_iff_iff.mpr
  rw [timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff,
    deterministicTableAcceptanceIndicator_eq_true_iff]
  exact (acceptsWithin_iff_accepting_run_at_horizon
    machine (tableBits table) T).symm

/-! ## The guarded fused realization of the unique component -/

/-- Fully explicit certificate that one master-guarded fused component
accepts.  Schedule validity and all blank-slab replay certificates are fields
of the proposition, rather than external reflection assumptions.  The final
Boolean is the actual total guarded compiled program on the supplied input. -/
def MasterGuardedFusedAcceptingComponentCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) : Prop :=
  TimedAlphaVisitScheduleValid (cachedInputMachine machine) alpha scheduled /\
    AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled /\
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) = true /\
    (cachedInputMachine machine).halt alpha.terminal.state = some .accept

/-- An accepting guarded fused certificate forces its advertised alpha to be
the chronological canonical alpha.  This uses the operational guarded
semantics and the rolling cut flags, not accepted-alpha uniqueness alone. -/
theorem masterGuardedFusedAcceptingComponentCertificate_alpha_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hcertificate : MasterGuardedFusedAcceptingComponentCertificate
      machine input alpha scheduled) :
    alpha = chronologicalTimedCanonicalAlpha
      (cachedInputMachine machine) input T b hb := by
  rcases hcertificate with ⟨hschedule, haccepted, heval, _hterminal⟩
  have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck
      (cachedInputMachine machine) input alpha scheduled = true :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      (cachedInputMachine machine) input alpha scheduled).2
        ⟨hschedule, haccepted⟩
  have hevalFold :=
    compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_timedAlphaFold_of_valid_acceptedFromBlank_canonical
      machine input alpha scheduled hschedule haccepted
  have hfold : timedAlphaInPlaceTwoWindowFoldCheck
      (cachedInputMachine machine) input alpha scheduled = true := by
    rw [← hevalFold]
    exact heval
  have hoffsets : alpha.offsets = canonicalCutOffsets
      (cachedInputMachine machine) input T b hb :=
    (timedAlphaInPlaceTwoWindowFoldCheck_eq_true_iff_offsets_eq
      (cachedInputMachine machine) input T b hb alpha scheduled hbase).1
        hfold
  exact timedAlphaVisitScheduleAllBlockVisitsCheck_eq_chronologicalAlpha
    (cachedInputMachine machine) input T b hb alpha scheduled hbase hoffsets

/-- The master-guarded fused component certificate is exact: such a
certificate exists iff the cached one-tape run accepts at the horizon. -/
theorem exists_masterGuardedFusedAcceptingComponentCertificate_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (exists alpha : AmbientTimedCanonicalAlpha
        (cachedInputMachine machine).State T b,
      exists scheduled : List (TimedAlphaScheduledVisit
        (cachedInputMachine machine).State T b),
        MasterGuardedFusedAcceptingComponentCertificate
          machine input alpha scheduled) <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  constructor
  · rintro ⟨alpha, scheduled, hcertificate⟩
    have halpha :=
      masterGuardedFusedAcceptingComponentCertificate_alpha_eq
        machine input T b hb alpha scheduled hcertificate
    have hterminal := hcertificate.2.2.2
    subst alpha
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using
      hterminal
  · intro haccept
    let cached := cachedInputMachine machine
    let alpha : AmbientTimedCanonicalAlpha cached.State T b :=
      chronologicalTimedCanonicalAlpha cached input T b hb
    obtain ⟨scheduled, hreplayed⟩ :=
      exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
        cached input T b hb
    have hinPlace : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        cached input alpha scheduled = true :=
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
        cached input T b hb alpha scheduled).2 (by
          simpa [alpha] using hreplayed)
    have hparts :
        timedAlphaVisitScheduleAllBlockVisitsCheck
            cached input alpha scheduled = true /\
          timedAlphaInPlaceTwoWindowFoldCheck
            cached input alpha scheduled = true := by
      simpa [timedAlphaVisitScheduleInPlaceCanonicalCutCheck] using hinPlace
    have hreflect :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        cached input alpha scheduled).1 hparts.1
    have hevalFold :=
      compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_timedAlphaFold_of_valid_acceptedFromBlank_canonical
        machine input alpha scheduled hreflect.1 hreflect.2
    have heval :
        (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := input.length) machine alpha scheduled).eval
            (fun index => input.get index) = true :=
      hevalFold.trans hparts.2
    have hterminal : cached.halt alpha.terminal.state = some .accept := by
      simpa [cached, alpha, IsAccepting, outcome,
        chronologicalTimedCanonicalAlpha] using haccept
    exact ⟨alpha, scheduled, hreflect.1, hreflect.2, heval, hterminal⟩

/-- The semantic single aggregate is therefore exactly the existential union
of genuine accepting total master-guarded fused component certificates. -/
theorem cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff_guardedFused
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    timedAlphaInPlaceAcceptingAggregateCheck
        (cachedInputMachine machine) input T b hb = true <->
      exists alpha : AmbientTimedCanonicalAlpha
          (cachedInputMachine machine).State T b,
        exists scheduled : List (TimedAlphaScheduledVisit
          (cachedInputMachine machine).State T b),
          MasterGuardedFusedAcceptingComponentCertificate
            machine input alpha scheduled := by
  rw [timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff]
  exact (exists_masterGuardedFusedAcceptingComponentCertificate_iff
    machine input T b hb).symm

/-- With the cache-normalization step included, the aggregate realized by the
guarded fused components is pointwise the original machine's bounded
acceptance indicator, with the exact one-step overhead. -/
theorem cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_baseAcceptanceIndicator
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n : Nat} (T b : Nat) (hb : 0 < b) (table : TruthTable n) :
    timedAlphaInPlaceAcceptingAggregateCheck (cachedInputMachine machine)
        (tableBits table) (T + 1) b hb =
      deterministicTableAcceptanceIndicator machine T table := by
  apply Bool.eq_iff_iff.mpr
  rw [timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff,
    cachedInputMachine_accepting_run_succ_iff,
    deterministicTableAcceptanceIndicator_eq_true_iff]
  exact (acceptsWithin_iff_accepting_run_at_horizon
    machine (tableBits table) T).symm

/-- Accepted guarded fused component certificates have a unique alpha even
when their exposed schedules differ. -/
theorem masterGuardedFusedAcceptingComponentCertificate_alpha_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {leftSchedule rightSchedule : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)}
    (hleft : MasterGuardedFusedAcceptingComponentCertificate
      machine input left leftSchedule)
    (hright : MasterGuardedFusedAcceptingComponentCertificate
      machine input right rightSchedule) :
    left = right := by
  rw [masterGuardedFusedAcceptingComponentCertificate_alpha_eq
      machine input T b hb left leftSchedule hleft,
    masterGuardedFusedAcceptingComponentCertificate_alpha_eq
      machine input T b hb right rightSchedule hright]

/-! ## A support HSG for this one aggregate -/

/-- Support-only hitting requirement for the single canonical aggregate.
Unlike a componentwise premise, this asks for just one hit after aggregation
and therefore contains no transcript-count error factor. -/
def HitsSingleCanonicalTimedAlphaAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b) : Prop :=
  DenseAboveHalf n (deterministicTableAcceptance machine T) ->
    exists seed : FiniteBitTape generator.seedBits,
      timedAlphaInPlaceAcceptingAggregateCheck machine
        (tableBits (generator.generate seed)) T b hb = true

/-- Hitting the one aggregate is exactly the existing dense-acceptance HSG
interface.  Thus aggregation introduces no additional semantic loss; the
missing work is to construct a local support hitting set for this predicate. -/
theorem hitsSingleCanonicalTimedAlphaAggregate_iff_hitsDenseOneTapeAcceptance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b) :
    HitsSingleCanonicalTimedAlphaAggregate machine generator T b hb <->
      HitsDenseOneTapeAcceptance machine generator T := by
  constructor
  · intro hhits hdense
    rcases hhits hdense with ⟨seed, haggregate⟩
    refine ⟨seed, ?_⟩
    exact (acceptsWithin_iff_accepting_run_at_horizon
      machine (tableBits (generator.generate seed)) T).2
      ((timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff
        machine (tableBits (generator.generate seed)) T b hb).1 haggregate)
  · intro hhits hdense
    rcases hhits hdense with ⟨seed, haccept⟩
    refine ⟨seed, ?_⟩
    apply (timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff
      machine (tableBits (generator.generate seed)) T b hb).2
    exact (acceptsWithin_iff_accepting_run_at_horizon
      machine (tableBits (generator.generate seed)) T).1 haccept

/-- Direct deterministic finite capstone stated only with a support HSG for
the single canonical aggregate. -/
theorem singleCanonicalTimedAlphaAggregateHSG_excludes_exactMCSPDecision
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hHits : HitsSingleCanonicalTimedAlphaAggregate
      (complementMachine machine) generator T b hb) :
    Not (ExactMCSPDecisionBehavior machine n threshold T) := by
  apply localGenerator_denseHitting_excludes_exactMCSPDecision
    machine generator T hLength
  exact
    (hitsSingleCanonicalTimedAlphaAggregate_iff_hitsDenseOneTapeAcceptance
      (complementMachine machine) generator T b hb).1 hHits

/-! ## The cache-normalized master-guarded aggregate endpoint -/

/-- Support hitting for the precise aggregate whose unique component is
realized by the total master-guarded fused compiler.  The aggregate uses the
cached machine for `T + 1` steps and is measured against density of the base
machine's `T`-step acceptance predicate. -/
def HitsSingleMasterGuardedCachedCanonicalAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b) : Prop :=
  DenseAboveHalf n (deterministicTableAcceptance machine T) ->
    exists seed : FiniteBitTape generator.seedBits,
      timedAlphaInPlaceAcceptingAggregateCheck (cachedInputMachine machine)
        (tableBits (generator.generate seed)) (T + 1) b hb = true

/-- Cache normalization makes the guarded-fused aggregate hitting premise
exactly equivalent to the original dense-acceptance HSG interface. -/
theorem hitsSingleMasterGuardedCachedCanonicalAggregate_iff_hitsDenseOneTapeAcceptance
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b) :
    HitsSingleMasterGuardedCachedCanonicalAggregate
        machine generator T b hb <->
      HitsDenseOneTapeAcceptance machine generator T := by
  constructor
  · intro hhits hdense
    rcases hhits hdense with ⟨seed, haggregate⟩
    refine ⟨seed, ?_⟩
    have heq :=
      cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_baseAcceptanceIndicator
        machine T b hb (generator.generate seed)
    rw [heq] at haggregate
    exact (deterministicTableAcceptanceIndicator_eq_true_iff
      machine T (generator.generate seed)).1 haggregate
  · intro hhits hdense
    rcases hhits hdense with ⟨seed, haccept⟩
    refine ⟨seed, ?_⟩
    rw [cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_baseAcceptanceIndicator
      machine T b hb (generator.generate seed)]
    exact (deterministicTableAcceptanceIndicator_eq_true_iff
      machine T (generator.generate seed)).2 haccept

/-- Deterministic MCSP capstone for a support HSG of the precise
cache-normalized master-guarded aggregate. -/
theorem singleMasterGuardedCachedCanonicalAggregateHSG_excludes_exactMCSPDecision
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hHits : HitsSingleMasterGuardedCachedCanonicalAggregate
      (complementMachine machine) generator T b hb) :
    Not (ExactMCSPDecisionBehavior machine n threshold T) := by
  apply localGenerator_denseHitting_excludes_exactMCSPDecision
    machine generator T hLength
  exact
    (hitsSingleMasterGuardedCachedCanonicalAggregate_iff_hitsDenseOneTapeAcceptance
      (complementMachine machine) generator T b hb).1 hHits

/-! ## One signed weighted approximation, with no union bound -/

/-- A signed weighted approximation for the single aggregate yields a
nonzero-weight accepting seed whenever bounded acceptance is dense.  There is
one approximation error, not a sum indexed by ambient alphas. -/
theorem signedWeightedApproximation_nonzeroSupport_hits_singleCanonicalAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hEpsilonNonnegative : 0 <= epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck machine
            (tableBits table) T b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck machine
              (tableBits table) T b hb)) <= epsilon)
    (hDense : DenseAboveHalf n (deterministicTableAcceptance machine T)) :
    exists seed : FiniteBitTape generator.seedBits,
      weight seed ≠ 0 /\
        timedAlphaInPlaceAcceptingAggregateCheck machine
          (tableBits (generator.generate seed)) T b hb = true := by
  let aggregate : TruthTable n -> Bool := fun table =>
    timedAlphaInPlaceAcceptingAggregateCheck machine
      (tableBits table) T b hb
  have hpointwise : aggregate =
      deterministicTableAcceptanceIndicator machine T := by
    funext table
    exact timedAlphaInPlaceAcceptingAggregateCheck_eq_acceptanceIndicator
      machine T b hb table
  have hmass : epsilon < uniformPredicateAverage aggregate := by
    rw [hpointwise]
    exact lt_trans hEpsilon
      (uniform_deterministicAcceptanceIndicator_gt_half
        machine T hDense)
  exact weightedApproximation_support_hits generator.generate weight
    aggregate epsilon hEpsilonNonnegative hApprox hmass

/-- The previous witness supplies precisely the support-HSG property for the
single canonical aggregate. -/
theorem signedWeightedApproximation_hits_singleCanonicalAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hEpsilonNonnegative : 0 <= epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck machine
            (tableBits table) T b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck machine
              (tableBits table) T b hb)) <= epsilon) :
    HitsSingleCanonicalTimedAlphaAggregate machine generator T b hb := by
  intro hdense
  rcases
      signedWeightedApproximation_nonzeroSupport_hits_singleCanonicalAggregate
        machine generator T b hb weight epsilon hEpsilonNonnegative hEpsilon
          hApprox hdense with
    ⟨seed, _hweight, haggregate⟩
  exact ⟨seed, haggregate⟩

/-- One signed approximation of the precise cache-normalized guarded-fused
aggregate supplies its support-HSG endpoint.  Again, the hypothesis contains
one scalar approximation error and no per-alpha family. -/
theorem signedWeightedApproximation_hits_singleMasterGuardedCachedCanonicalAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hEpsilonNonnegative : 0 <= epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck (cachedInputMachine machine)
            (tableBits table) (T + 1) b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck
              (cachedInputMachine machine) (tableBits table) (T + 1) b hb)) <=
        epsilon) :
    HitsSingleMasterGuardedCachedCanonicalAggregate
      machine generator T b hb := by
  intro hdense
  let aggregate : TruthTable n -> Bool := fun table =>
    timedAlphaInPlaceAcceptingAggregateCheck (cachedInputMachine machine)
      (tableBits table) (T + 1) b hb
  have hpointwise : aggregate =
      deterministicTableAcceptanceIndicator machine T := by
    funext table
    exact
      cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_baseAcceptanceIndicator
        machine T b hb table
  have hmass : epsilon < uniformPredicateAverage aggregate := by
    rw [hpointwise]
    exact lt_trans hEpsilon
      (uniform_deterministicAcceptanceIndicator_gt_half
        machine T hdense)
  rcases weightedApproximation_support_hits generator.generate weight
      aggregate epsilon hEpsilonNonnegative hApprox hmass with
    ⟨seed, _hweight, haggregate⟩
  exact ⟨seed, haggregate⟩

/-- Direct MCSP contradiction from one signed approximation of the single
guarded-canonical aggregate of the complemented machine.  No per-alpha
approximation premise and no union bound occur in the theorem. -/
theorem signedWeightedSingleCanonicalAggregateApproximation_excludes_exactMCSPDecision
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hEpsilonNonnegative : 0 <= epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck (complementMachine machine)
            (tableBits table) T b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck
              (complementMachine machine) (tableBits table) T b hb)) <=
        epsilon) :
    Not (ExactMCSPDecisionBehavior machine n threshold T) := by
  apply singleCanonicalTimedAlphaAggregateHSG_excludes_exactMCSPDecision
    machine generator T b hb hLength
  exact signedWeightedApproximation_hits_singleCanonicalAggregate
    (complementMachine machine) generator T b hb weight epsilon
      hEpsilonNonnegative hEpsilon hApprox

/-- Strongest direct endpoint for the implemented lower layer: a single
signed approximation of the cache-normalized aggregate represented by the
total master-guarded fused components excludes exact MCSP decision.  The
unproved obligation is construction/locality of that aggregate WPRG, not any
sum of component errors. -/
theorem signedWeightedSingleMasterGuardedCachedCanonicalAggregateApproximation_excludes_exactMCSPDecision
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n threshold : Nat} (generator : DAGLocalGenerator n threshold)
    (T b : Nat) (hb : 0 < b)
    (weight : FiniteBitTape generator.seedBits -> Rat)
    (epsilon : Rat)
    (hLength : DAGCodec.codeLength n threshold + 2 < 2 ^ n)
    (hEpsilonNonnegative : 0 <= epsilon)
    (hEpsilon : epsilon < (1 : Rat) / 2)
    (hApprox :
      abs (uniformPredicateAverage (fun table : TruthTable n =>
          timedAlphaInPlaceAcceptingAggregateCheck
            (cachedInputMachine (complementMachine machine))
            (tableBits table) (T + 1) b hb) -
        weightedGeneratorAverage generator.generate weight
          (fun table : TruthTable n =>
            timedAlphaInPlaceAcceptingAggregateCheck
              (cachedInputMachine (complementMachine machine))
              (tableBits table) (T + 1) b hb)) <= epsilon) :
    Not (ExactMCSPDecisionBehavior machine n threshold T) := by
  apply
    singleMasterGuardedCachedCanonicalAggregateHSG_excludes_exactMCSPDecision
      machine generator T b hb hLength
  exact
    signedWeightedApproximation_hits_singleMasterGuardedCachedCanonicalAggregate
      (complementMachine machine) generator T b hb weight epsilon
        hEpsilonNonnegative hEpsilon hApprox

end OneTapeMagnification
end Frontier
end Pnp4
