import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.GuardedFiniteCachedAllBlocksReadOnce
import Pnp4.Frontier.OneTapeMagnification.FixedVisitFreshPrefixSync
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedVisitCorrectness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact adaptive query traces and the accepted master-order residual

This module supplies a trace-sensitive counterpart of the existing adaptive
state simulation.  It records the coordinates exposed by adaptive layers,
compresses exact silent/query microstep certificates, and isolates the final
accepted-schedule theorem as an exact coordinate-order statement.
-/

namespace FiniteStreamingVerifier

variable {Symbol : Type}

/-- Coordinates exposed by `layers` adaptive iterations from an arbitrary
fueled state.  The recursion is deliberately aligned with
`runAdaptiveFrom`: first execute the shorter prefix, then append its next
query. -/
def adaptiveQueryTraceFrom (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) : Nat → verifier.FueledState H → List (Fin n)
  | 0, _ => []
  | layers + 1, state =>
      let previous := verifier.runAdaptiveFrom encode queryIndex? input
        layers state
      verifier.adaptiveQueryTraceFrom encode queryIndex? input layers state ++
        (verifier.adaptiveQuery? queryIndex? previous).toList

/-- Although `adaptiveQueryTraceFrom` is prefix-recursive, it may equivalently
expose the first adaptive query and continue from the first successor. -/
theorem adaptiveQueryTraceFrom_succ_front
    (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (layers : Nat)
    (state : verifier.FueledState H) :
    verifier.adaptiveQueryTraceFrom encode queryIndex? input (layers + 1)
        state =
      (verifier.adaptiveQuery? queryIndex? state).toList ++
        verifier.adaptiveQueryTraceFrom encode queryIndex? input layers
          (verifier.adaptiveInputStep encode queryIndex? input state) := by
  induction layers generalizing state with
  | zero =>
      simp [adaptiveQueryTraceFrom, runAdaptiveFrom]
  | succ layers ih =>
      change
        (verifier.adaptiveQueryTraceFrom encode queryIndex? input
              (layers + 1) state ++
            (verifier.adaptiveQuery? queryIndex?
              (verifier.runAdaptiveFrom encode queryIndex? input
                (layers + 1) state)).toList) = _
      rw [ih state]
      rw [verifier.runAdaptiveFrom_succ_front encode queryIndex? input]
      simp only [adaptiveQueryTraceFrom]
      simp [List.append_assoc]

/-- The coordinate component of every compiled prefix is exactly the adaptive
trace just defined. -/
theorem compileAdaptive_executePrefix_trace
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (k : Nat) (hk : k ≤ H) :
    ((verifier.compileAdaptive H n encode endSymbol queryIndex?).executePrefix
      input k hk).2 =
      verifier.adaptiveQueryTraceFrom encode queryIndex? input k
        (verifier.initialFueledState H) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [LayeredQueryProgram.executePrefix, adaptiveQueryTraceFrom]
      rw [ih (by omega)]
      rw [verifier.compileAdaptive_executePrefix_state H n encode endSymbol
        queryIndex? input k (by omega)]
      rfl

/-- Full compiled query trace in verifier-native form. -/
theorem compileAdaptive_queryTrace
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) :
    (verifier.compileAdaptive H n encode endSymbol queryIndex?).queryTrace
        input =
      verifier.adaptiveQueryTraceFrom encode queryIndex? input H
        (verifier.initialFueledState H) := by
  exact verifier.compileAdaptive_executePrefix_trace H n encode endSymbol
    queryIndex? input H le_rfl

/-- A microstep certificate that remembers exact query coordinates as well as
the supplied Boolean bits. -/
inductive ExactAdaptiveQueryOrder
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) :
    Nat → verifier.State → List (Fin n) → verifier.State → Prop
  | halted (state : verifier.State)
      (hhalted : verifier.halted state = true) :
      ExactAdaptiveQueryOrder verifier encode queryIndex? input
        0 state [] state
  | silent {steps : Nat} {state target : verifier.State}
      {queries : List (Fin n)}
      (hhalted : verifier.halted state = false)
      (hrequest : verifier.requestsInput state = false)
      (tail : ExactAdaptiveQueryOrder verifier encode queryIndex? input
        steps (verifier.step state none) queries target) :
      ExactAdaptiveQueryOrder verifier encode queryIndex? input
        (steps + 1) state queries target
  | query {steps : Nat} {state target : verifier.State}
      {index : Fin n} {bit : Bool} {queries : List (Fin n)}
      (hhalted : verifier.halted state = false)
      (hrequest : verifier.requestsInput state = true)
      (hselector : queryIndex? state = some index)
      (hbit : input index = bit)
      (tail : ExactAdaptiveQueryOrder verifier encode queryIndex? input
        steps (verifier.step state (some (encode bit))) queries target) :
      ExactAdaptiveQueryOrder verifier encode queryIndex? input
        (steps + 1) state (index :: queries) target

/-- An exact query-order certificate contains no more queries than
microsteps. -/
theorem ExactAdaptiveQueryOrder.queryCount_le_steps
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) {steps : Nat} {state target : verifier.State}
    {queries : List (Fin n)}
    (trace : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      steps state queries target) :
    queries.length ≤ steps := by
  induction trace with
  | halted => simp
  | silent _ _ tail ih => simpa using Nat.le_succ_of_le ih
  | query _ _ _ _ tail ih => simpa using Nat.succ_le_succ ih

/-- Every exact coordinate certificate ends in a halted verifier state. -/
theorem ExactAdaptiveQueryOrder.target_halted
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) {steps : Nat} {state target : verifier.State}
    {queries : List (Fin n)}
    (trace : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      steps state queries target) :
    verifier.halted target = true := by
  induction trace with
  | halted _ hhalted => exact hhalted
  | silent _ _ _ ih => exact ih
  | query _ _ _ _ _ ih => exact ih

/-- A certificate starting in an already halted state cannot contain a
query coordinate. -/
theorem ExactAdaptiveQueryOrder.queries_eq_nil_of_halted
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) {steps : Nat} {state target : verifier.State}
    {queries : List (Fin n)}
    (trace : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      steps state queries target)
    (hhalted : verifier.halted state = true) :
    queries = [] := by
  cases trace with
  | halted => rfl
  | silent hhaltedFalse _ _ => simp [hhalted] at hhaltedFalse
  | query hhaltedFalse _ _ _ _ => simp [hhalted] at hhaltedFalse

/-- Exact adaptive executions from the same verifier state expose the same
coordinate list.  Halting/request bits choose the constructor uniquely, and
the selector plus canonical input choose the queried coordinate and bit. -/
theorem ExactAdaptiveQueryOrder.queries_eq_of_same_start
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool)
    {firstSteps secondSteps : Nat} {state firstTarget secondTarget : verifier.State}
    {firstQueries secondQueries : List (Fin n)}
    (first : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      firstSteps state firstQueries firstTarget)
    (second : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      secondSteps state secondQueries secondTarget) :
    firstQueries = secondQueries := by
  induction first generalizing secondSteps secondQueries secondTarget with
  | halted state hhalted =>
      exact
        (ExactAdaptiveQueryOrder.queries_eq_nil_of_halted verifier encode
          queryIndex? input second hhalted).symm
  | @silent steps state firstTarget queries hhalted hrequest tail ih =>
      cases second with
      | halted _ secondHalted => simp [secondHalted] at hhalted
      | silent _ secondRequest secondTail =>
          exact ih secondTail
      | query _ secondRequest _ _ _ =>
          simp [hrequest] at secondRequest
  | @query steps state firstTarget index bit queries hhalted hrequest
      hselector hbit tail ih =>
      cases second with
      | halted _ secondHalted => simp [secondHalted] at hhalted
      | silent _ secondRequest _ => simp [hrequest] at secondRequest
      | @query secondSteps _ secondTarget secondIndex secondBit secondQueries
          _ _ secondSelector secondBitValue secondTail =>
          have hindex : secondIndex = index := by
            rw [hselector] at secondSelector
            exact (Option.some.inj secondSelector).symm
          subst secondIndex
          have hbitEq : secondBit = bit := by
            rw [hbit] at secondBitValue
            exact secondBitValue.symm
          subst secondBit
          exact congrArg (index :: ·) (ih (by simpa [hbit] using secondTail))

/-- An exact fresh-answer trace cannot leave a state which is already
halted. -/
theorem ExactFreshTrace.eq_of_halted_start
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {steps : Nat} {state target : verifier.State} {answers : List Bool}
    (trace : ExactFreshTrace verifier encode steps state answers target)
    (hhalted : verifier.halted state = true) :
    steps = 0 ∧ answers = [] ∧ target = state := by
  cases trace with
  | halted => exact ⟨rfl, rfl, rfl⟩
  | silent hhaltedFalse _ _ => simp [hhalted] at hhaltedFalse
  | query hhaltedFalse _ _ => simp [hhalted] at hhaltedFalse

/-- An exact Boolean-answer trace determines an exact coordinate trace when
the verifier exposes a rank whose silent steps stutter and whose querying
steps select, then increment, the current rank. -/
theorem ExactFreshTrace.toExactAdaptiveQueryOrder_of_rank
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (rank : verifier.State → Nat)
    {steps : Nat} {state target : verifier.State} {answers : List Bool}
    (hsilentOrder : ∀ {tailSteps : Nat} {current : verifier.State}
        {tailAnswers : List Bool},
      verifier.halted current = false →
      verifier.requestsInput current = false →
      ExactFreshTrace verifier encode tailSteps
        (verifier.step current none) tailAnswers target →
      finiteInputVariableQueryOrder n
          (List.range' (rank current) (rank target - rank current)) =
        finiteInputVariableQueryOrder n
          (List.range' (rank (verifier.step current none))
            (rank target - rank (verifier.step current none))))
    (hquerySelector : ∀ state,
      verifier.halted state = false →
      verifier.requestsInput state = true →
      ∃ hbound : rank state < n,
        queryIndex? state = some ⟨rank state, hbound⟩)
    (hqueryRank : ∀ {tailSteps : Nat} {current : verifier.State}
        {tailAnswers : List Bool} (bit : Bool),
      verifier.halted current = false →
      verifier.requestsInput current = true →
      ExactFreshTrace verifier encode tailSteps
        (verifier.step current (some (encode bit))) tailAnswers target →
      rank (verifier.step current (some (encode bit))) = rank current + 1)
    (trace : ExactFreshTrace verifier encode steps state answers target)
    (hanswers : answers =
      (finiteInputVariableQueryOrder n
        (List.range' (rank state) (rank target - rank state))).map input) :
    ExactAdaptiveQueryOrder verifier encode queryIndex? input steps state
      (finiteInputVariableQueryOrder n
        (List.range' (rank state) (rank target - rank state))) target := by
  revert hanswers
  induction trace with
  | halted state hhalted =>
      intro _
      simpa [finiteInputVariableQueryOrder] using
        (ExactAdaptiveQueryOrder.halted (queryIndex? := queryIndex?)
          (input := input) state hhalted)
  | @silent steps state target answers hhalted hrequest tail ih =>
      intro hanswers
      have horder := hsilentOrder hhalted hrequest tail
      have htailAnswers : answers =
          (finiteInputVariableQueryOrder n
            (List.range' (rank (verifier.step state none))
              (rank target - rank (verifier.step state none)))).map input := by
        rw [← horder]
        exact hanswers
      have htail := ih hsilentOrder hqueryRank htailAnswers
      rw [horder]
      exact ExactAdaptiveQueryOrder.silent hhalted hrequest htail
  | @query steps state target bit answers hhalted hrequest tail ih =>
      intro hanswers
      obtain ⟨hbound, hselector⟩ :=
        hquerySelector state hhalted hrequest
      have hlt : rank state < rank target := by
        by_contra hnot
        have hle : rank target ≤ rank state := Nat.le_of_not_gt hnot
        have hzero : rank target - rank state = 0 :=
          Nat.sub_eq_zero_of_le hle
        simp [hzero, finiteInputVariableQueryOrder] at hanswers
      have hinterval := finiteInputVariableQueryOrder_interval_cons
        hbound hlt
      rw [hinterval] at hanswers
      simp only [List.map_cons] at hanswers
      have hbit : input ⟨rank state, hbound⟩ = bit :=
        (List.cons.inj hanswers).1.symm
      have htailAnswers : answers =
          (finiteInputVariableQueryOrder n
            (List.range' (rank state + 1)
              (rank target - (rank state + 1)))).map input :=
        (List.cons.inj hanswers).2
      have hrank :
          rank (verifier.step state (some (encode bit))) = rank state + 1 :=
        hqueryRank bit hhalted hrequest tail
      rw [hinterval]
      apply ExactAdaptiveQueryOrder.query hhalted hrequest hselector hbit
      have htail := ih hsilentOrder hqueryRank
        (by simpa [hrank] using htailAnswers)
      simpa [hrank] using htail

/-- A halted verifier exposes no adaptive coordinates, regardless of the
number of unused program layers. -/
theorem adaptiveQueryTraceFrom_eq_nil_of_halted
    (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (layers : Nat)
    (state : verifier.FueledState H)
    (hhalted : verifier.halted state.1 = true) :
    verifier.adaptiveQueryTraceFrom encode queryIndex? input layers state =
      [] := by
  induction layers generalizing state with
  | zero => rfl
  | succ layers ih =>
      have hclosed := verifier.silentClosure_eq_self_of_halted state hhalted
      have hquery : verifier.adaptiveQuery? queryIndex? state = none := by
        simp [adaptiveQuery?, hclosed, hhalted]
      have hnext := verifier.adaptiveInputStep_eq_self_of_halted encode
        queryIndex? input state hhalted
      rw [verifier.adaptiveQueryTraceFrom_succ_front encode queryIndex? input]
      rw [hquery, hnext, ih state hhalted]
      rfl

/-- Removing one certified leading silent microstep does not change any
future adaptive coordinate trace. -/
theorem adaptiveQueryTraceFrom_eq_of_leading_silent
    (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (layers : Nat)
    (state : verifier.State) (fuel : Fin (H + 1))
    (hpositive : 0 < fuel.val)
    (hhalted : verifier.halted state = false)
    (hrequest : verifier.requestsInput state = false) :
    verifier.adaptiveQueryTraceFrom encode queryIndex? input layers
        (state, fuel) =
      verifier.adaptiveQueryTraceFrom encode queryIndex? input layers
        (verifier.step state none, spendOne fuel) := by
  have hclosed := verifier.silentClosure_eq_silentClosure_step_none
    state fuel hpositive hhalted hrequest
  have hquery : verifier.adaptiveQuery? queryIndex? (state, fuel) =
      verifier.adaptiveQuery? queryIndex?
        (verifier.step state none, spendOne fuel) := by
    simp only [adaptiveQuery?]
    rw [hclosed]
  have hnext : verifier.adaptiveInputStep encode queryIndex? input
      (state, fuel) =
      verifier.adaptiveInputStep encode queryIndex? input
        (verifier.step state none, spendOne fuel) := by
    simp only [adaptiveInputStep, adaptiveNext]
    rw [hclosed, hquery]
  cases layers with
  | zero => rfl
  | succ layers =>
      rw [verifier.adaptiveQueryTraceFrom_succ_front encode queryIndex? input]
      rw [verifier.adaptiveQueryTraceFrom_succ_front encode queryIndex? input]
      rw [hquery, hnext]

/-- Exact microstep coordinate certificates are realized literally by the
adaptive trace whenever enough fuel and adaptive layers are available. -/
theorem ExactAdaptiveQueryOrder.adaptiveQueryTraceFrom_eq
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {H n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) {steps : Nat} {state target : verifier.State}
    {queries : List (Fin n)}
    (trace : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      steps state queries target)
    (fuel : Fin (H + 1)) (hsteps : steps ≤ fuel.val)
    (layers : Nat) (hqueries : queries.length ≤ layers) :
    verifier.adaptiveQueryTraceFrom encode queryIndex? input layers
        (state, fuel) = queries := by
  induction trace generalizing fuel layers with
  | halted state hhalted =>
      exact verifier.adaptiveQueryTraceFrom_eq_nil_of_halted encode
        queryIndex? input layers (state, fuel) hhalted
  | @silent steps state target queries hhalted hrequest tail ih =>
      have hpositive : 0 < fuel.val := by omega
      rw [verifier.adaptiveQueryTraceFrom_eq_of_leading_silent encode
        queryIndex? input layers state fuel hpositive hhalted hrequest]
      apply ih (spendOne fuel)
      · simp only [spendOne]
        omega
      · exact hqueries
  | @query steps state target index bit queries hhalted hrequest hselector
      hbit tail ih =>
      have hpositive : 0 < fuel.val := by omega
      cases layers with
      | zero => simp at hqueries
      | succ layers =>
          have hclosed := verifier.silentClosure_eq_self_of_requestsInput
            state fuel hrequest
          have hquery : verifier.adaptiveQuery? queryIndex? (state, fuel) =
              some index := by
            simp [adaptiveQuery?, hclosed, hpositive, hhalted, hrequest,
              hselector]
          have hnext : verifier.adaptiveInputStep encode queryIndex? input
              (state, fuel) =
                (verifier.step state (some (encode bit)), spendOne fuel) := by
            simp [adaptiveInputStep, adaptiveNext, hquery, hclosed, hbit]
          rw [verifier.adaptiveQueryTraceFrom_succ_front encode queryIndex?
            input, hquery, hnext]
          simp only [Option.toList_some, List.singleton_append]
          apply congrArg (index :: ·)
          apply ih (spendOne fuel)
          · simp only [spendOne]
            omega
          · simpa using hqueries

/-- A full exact certificate from the verifier start fixes the complete query
trace of its compiled adaptive program. -/
theorem ExactAdaptiveQueryOrder.compileAdaptive_queryTrace_eq
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    (endSymbol : Symbol) {H n : Nat}
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) {steps : Nat} {target : verifier.State}
    {queries : List (Fin n)}
    (trace : ExactAdaptiveQueryOrder verifier encode queryIndex? input
      steps verifier.start queries target)
    (hsteps : steps ≤ H) :
    (verifier.compileAdaptive H n encode endSymbol queryIndex?).queryTrace
        input = queries := by
  rw [verifier.compileAdaptive_queryTrace H n encode endSymbol queryIndex?
    input]
  apply ExactAdaptiveQueryOrder.adaptiveQueryTraceFrom_eq verifier encode
    queryIndex? input trace
    (⟨H, Nat.lt_succ_self H⟩ : Fin (H + 1)) hsteps H
  exact (ExactAdaptiveQueryOrder.queryCount_le_steps verifier encode
    queryIndex? input trace).trans hsteps

/-- A halted ordinary input-driven execution always carries an exact
coordinate certificate.  The certificate may use fewer microsteps than the
supplied fuel only when the execution reached a halted state early. -/
theorem exists_exactAdaptiveQueryOrder_of_inputDrivenCore_halted
    (verifier : FiniteStreamingVerifier Symbol) (encode : Bool → Symbol)
    {n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool)
    (htotal : ∀ state, verifier.requestsInput state = true →
      ∃ index, queryIndex? state = some index)
    (fuel : Nat) (state : verifier.State)
    (hfinal : verifier.halted
      (verifier.inputDrivenCore encode queryIndex? input fuel state) = true) :
    ∃ steps queries,
      steps ≤ fuel ∧
        ExactAdaptiveQueryOrder verifier encode queryIndex? input
          steps state queries
            (verifier.inputDrivenCore encode queryIndex? input fuel state) := by
  induction fuel generalizing state with
  | zero =>
      refine ⟨0, [], le_rfl, ?_⟩
      apply ExactAdaptiveQueryOrder.halted
      simpa [inputDrivenCore] using hfinal
  | succ fuel ih =>
      by_cases hhalt : verifier.halted state = true
      · have hcore : verifier.inputDrivenCore encode queryIndex? input
            (fuel + 1) state = state :=
          verifier.inputDrivenCore_eq_self_of_halted encode queryIndex? input
            (fuel + 1) state hhalt
        refine ⟨0, [], by omega, ?_⟩
        rw [hcore]
        exact ExactAdaptiveQueryOrder.halted state hhalt
      · have hhaltFalse : verifier.halted state = false := by
          cases h : verifier.halted state <;> simp_all
        by_cases hrequest : verifier.requestsInput state = true
        · obtain ⟨index, hindex⟩ := htotal state hrequest
          let next := verifier.step state (some (encode (input index)))
          have hcore : verifier.inputDrivenCore encode queryIndex? input
              (fuel + 1) state =
                verifier.inputDrivenCore encode queryIndex? input fuel next := by
            simp [inputDrivenCore, hhaltFalse, hrequest, hindex, next]
          have hfinalNext : verifier.halted
              (verifier.inputDrivenCore encode queryIndex? input fuel next) =
                true := by
            rw [hcore] at hfinal
            exact hfinal
          obtain ⟨steps, queries, hsteps, htrace⟩ := ih next hfinalNext
          refine ⟨steps + 1, index :: queries, by omega, ?_⟩
          rw [hcore]
          exact ExactAdaptiveQueryOrder.query hhaltFalse hrequest hindex rfl
            htrace
        · have hrequestFalse : verifier.requestsInput state = false := by
            cases h : verifier.requestsInput state <;> simp_all
          let next := verifier.step state none
          have hcore : verifier.inputDrivenCore encode queryIndex? input
              (fuel + 1) state =
                verifier.inputDrivenCore encode queryIndex? input fuel next := by
            simp [inputDrivenCore, hhaltFalse, hrequestFalse, next]
          have hfinalNext : verifier.halted
              (verifier.inputDrivenCore encode queryIndex? input fuel next) =
                true := by
            rw [hcore] at hfinal
            exact hfinal
          obtain ⟨steps, queries, hsteps, htrace⟩ := ih next hfinalNext
          refine ⟨steps + 1, queries, by omega, ?_⟩
          rw [hcore]
          exact ExactAdaptiveQueryOrder.silent hhaltFalse hrequestFalse htrace

/-- Map an exact coordinate trace through a verifier-state embedding and
replace its terminal halted constructor by a continuation trace. -/
theorem ExactAdaptiveQueryOrder.map_append
    (source targetVerifier : FiniteStreamingVerifier Symbol)
    (encode : Bool → Symbol) {n : Nat}
    (sourceQueryIndex? : source.State → Option (Fin n))
    (targetQueryIndex? : targetVerifier.State → Option (Fin n))
    (input : Fin n → Bool) (embed : source.State → targetVerifier.State)
    (hhalted : ∀ state, source.halted state = false →
      targetVerifier.halted (embed state) = false)
    (hrequests : ∀ state, source.halted state = false →
      targetVerifier.requestsInput (embed state) =
        source.requestsInput state)
    (hselector : ∀ state, source.halted state = false →
      targetQueryIndex? (embed state) = sourceQueryIndex? state)
    (hstep : ∀ state supplied, source.halted state = false →
      targetVerifier.step (embed state) supplied =
        embed (source.step state supplied))
    {firstSteps : Nat} {start middle : source.State}
    {firstQueries : List (Fin n)}
    (first : ExactAdaptiveQueryOrder source encode sourceQueryIndex? input
      firstSteps start firstQueries middle)
    {secondSteps : Nat} {secondQueries : List (Fin n)}
    {final : targetVerifier.State}
    (second : ExactAdaptiveQueryOrder targetVerifier encode targetQueryIndex?
      input secondSteps (embed middle) secondQueries final) :
    ExactAdaptiveQueryOrder targetVerifier encode targetQueryIndex? input
      (firstSteps + secondSteps) (embed start)
      (firstQueries ++ secondQueries) final := by
  induction first with
  | halted state sourceHalted =>
      simpa using second
  | @silent steps state middle queries sourceHalted sourceRequest tail ih =>
      have targetHalted := hhalted state sourceHalted
      have targetRequest :
          targetVerifier.requestsInput (embed state) = false := by
        rw [hrequests state sourceHalted]
        exact sourceRequest
      have mappedTail := ih second
      rw [← hstep state none sourceHalted] at mappedTail
      have result := ExactAdaptiveQueryOrder.silent targetHalted targetRequest
        mappedTail
      simpa [Nat.add_assoc, Nat.add_comm secondSteps 1] using result
  | @query steps state middle index bit queries sourceHalted sourceRequest
      sourceSelector sourceBit tail ih =>
      have targetHalted := hhalted state sourceHalted
      have targetRequest :
          targetVerifier.requestsInput (embed state) = true := by
        rw [hrequests state sourceHalted]
        exact sourceRequest
      have targetSelector : targetQueryIndex? (embed state) = some index := by
        rw [hselector state sourceHalted]
        exact sourceSelector
      have mappedTail := ih second
      rw [← hstep state (some (encode bit)) sourceHalted] at mappedTail
      have result := ExactAdaptiveQueryOrder.query targetHalted targetRequest
        targetSelector sourceBit mappedTail
      simpa [Nat.add_assoc, Nat.add_comm secondSteps 1] using result

end FiniteStreamingVerifier

namespace LayeredQueryProgram

/-- Every executed prefix is literally an initial segment of every longer
execution on the same input. -/
theorem executePrefix_trace_append_of_le
    {n L : Nat} (program : LayeredQueryProgram n L)
    (input : Fin n → Bool) (k later : Nat)
    (hk : k ≤ L) (hlater : later ≤ L) (hkl : k ≤ later) :
    ∃ suffix,
      (program.executePrefix input later hlater).2 =
        (program.executePrefix input k hk).2 ++ suffix := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hkl
  induction extra with
  | zero =>
      refine ⟨[], ?_⟩
      simp
  | succ extra ih =>
      have hexists : ∃ suffix,
          (program.executePrefix input (k + extra) (by omega)).2 =
            (program.executePrefix input k hk).2 ++ suffix :=
        ih (by omega) (by omega)
      obtain ⟨suffix, hsuffix⟩ := hexists
      let previous := program.executePrefix input (k + extra) (by omega)
      let layer : Fin L := ⟨k + extra, by omega⟩
      let query := program.query? layer previous.1
      refine ⟨suffix ++ query.toList, ?_⟩
      simp only [LayeredQueryProgram.executePrefix]
      change previous.2 ++ query.toList =
        (program.executePrefix input k hk).2 ++ (suffix ++ query.toList)
      rw [show previous.2 =
        (program.executePrefix input k hk).2 ++ suffix by
          simpa [previous] using hsuffix]
      simp [List.append_assoc]

/-- Exact full-trace equality is sufficient for the input-specific
`ExecutionQueriesFollowMaster` premise used by the guarded compiler. -/
theorem executionQueriesFollowMaster_of_queryTrace_eq
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n → Bool)
    (htrace : program.queryTrace input = master) :
    ExecutionQueriesFollowMaster program master input := by
  intro k hk
  let previous := program.executePrefix input k (Nat.le_of_lt hk)
  let layer : Fin L := ⟨k, hk⟩
  let query := program.query? layer previous.1
  change
    match query with
    | none => True
    | some coordinate =>
        ∃ hlength : previous.2.length < master.length,
          master.get ⟨previous.2.length, hlength⟩ = coordinate
  cases hquery : query with
  | none => trivial
  | some coordinate =>
      have hnextTrace :
          (program.executePrefix input (k + 1) (by omega)).2 =
            previous.2 ++ [coordinate] := by
        simp only [LayeredQueryProgram.executePrefix]
        simp [previous, layer, query, hquery]
      obtain ⟨suffix, hsuffix⟩ :=
        executePrefix_trace_append_of_le program input (k + 1) L
          (by omega) le_rfl (by omega)
      have hmaster : master = (previous.2 ++ [coordinate]) ++ suffix := by
        calc
          master = program.queryTrace input := htrace.symm
          _ = (program.executePrefix input L le_rfl).2 := rfl
          _ = (program.executePrefix input (k + 1) (by omega)).2 ++
                suffix := hsuffix
          _ = (previous.2 ++ [coordinate]) ++ suffix := by rw [hnextTrace]
      clear htrace
      cases hmaster
      refine ⟨by simp, ?_⟩
      simp

/-- An exact adaptive microstep certificate therefore discharges the guarded
master-order residual directly. -/
theorem executionQueriesFollowMaster_of_exactAdaptiveQueryOrder
    {Symbol : Type} (verifier : FiniteStreamingVerifier Symbol)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    {H n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) {steps : Nat} {target : verifier.State}
    {master : List (Fin n)}
    (trace : FiniteStreamingVerifier.ExactAdaptiveQueryOrder verifier encode
      queryIndex? input steps verifier.start master target)
    (hsteps : steps ≤ H) :
    ExecutionQueriesFollowMaster
      (verifier.compileAdaptive H n encode endSymbol queryIndex?) master
      input := by
  apply executionQueriesFollowMaster_of_queryTrace_eq
  exact trace.compileAdaptive_queryTrace_eq verifier encode endSymbol
    queryIndex? input hsteps

end LayeredQueryProgram

/-- For the one-visit verifier, every exact canonical fresh-answer trace has
the exact clipped input-head coordinate interval. -/
theorem finiteCachedVisitExactFreshTrace_toExactAdaptiveQueryOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {H w base : Nat}
    (hbound : base + w ≤ H + 1)
    (initialRemaining : Fin (H + 1))
    (initialLive : LocalReplayState
      (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    {steps : Nat}
    {phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w}
    {answers : List Bool}
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (trace :
      let verifier := finiteCachedVisitStreamingVerifier machine input.length
        H w base hbound initialRemaining initialLive expected
      FiniteStreamingVerifier.ExactFreshTrace verifier
        (fun bit => .bit bit) steps phase answers (.completed final))
    (hanswers : answers =
      (finiteInputVariableQueryOrder input.length
        (List.range' (finiteCachedVisitPhaseInputRank phase)
          (final.inputHead.val -
            finiteCachedVisitPhaseInputRank phase))).map
              (fun index => input.get index)) :
    let verifier := finiteCachedVisitStreamingVerifier machine input.length
      H w base hbound initialRemaining initialLive expected
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder verifier
      (fun bit => .bit bit)
      (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) steps phase
      (finiteInputVariableQueryOrder input.length
        (List.range' (finiteCachedVisitPhaseInputRank phase)
          (final.inputHead.val - finiteCachedVisitPhaseInputRank phase)))
      (.completed final) := by
  let verifier := finiteCachedVisitStreamingVerifier machine input.length
    H w base hbound initialRemaining initialLive expected
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedVisitAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let rank : verifier.State → Nat := finiteCachedVisitPhaseInputRank
  change FiniteStreamingVerifier.ExactFreshTrace verifier
    (fun bit => .bit bit) steps phase answers (.completed final) at trace
  change answers =
    (finiteInputVariableQueryOrder input.length
      (List.range' (rank phase)
        (rank (.completed final) - rank phase))).map inputBits at hanswers
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder verifier
    (fun bit => .bit bit) selector inputBits steps phase
    (finiteInputVariableQueryOrder input.length
      (List.range' (rank phase)
        (rank (.completed final) - rank phase))) (.completed final)
  have hquerySelector : ∀ state,
      verifier.halted state = false →
      verifier.requestsInput state = true →
      ∃ hhead : rank state < input.length,
        selector state = some ⟨rank state, hhead⟩ := by
    intro state _hhalt hrequest
    cases state with
    | completed completed =>
        simp [verifier, finiteCachedVisitStreamingVerifier,
          finiteCachedVisitPhaseRequestsInput] at hrequest
    | rejected failure =>
        simp [verifier, finiteCachedVisitStreamingVerifier,
          finiteCachedVisitPhaseRequestsInput] at hrequest
    | running remaining live =>
        have hrequestData :=
          (finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
            machine input.length remaining live).mp hrequest
        refine ⟨hrequestData.2.2, ?_⟩
        simp [selector, rank, finiteCachedVisitAdaptiveQueryIndex?,
          finiteCachedVisitPhaseInputRank, hrequestData.2.2]
  have hqueryRank : ∀ {tailSteps : Nat} {state : verifier.State}
      {tailAnswers : List Bool} (bit : Bool),
      verifier.halted state = false →
      verifier.requestsInput state = true →
      FiniteStreamingVerifier.ExactFreshTrace verifier
        (fun bit => .bit bit) tailSteps
        (verifier.step state (some (.bit bit))) tailAnswers
        (.completed final) →
      rank (verifier.step state (some (.bit bit))) = rank state + 1 := by
    intro tailSteps state tailAnswers bit hhalt hrequest htail
    cases state with
    | completed completed =>
        simp [verifier, finiteCachedVisitStreamingVerifier,
          finiteCachedVisitPhaseRequestsInput] at hrequest
    | rejected failure =>
        simp [verifier, finiteCachedVisitStreamingVerifier,
          finiteCachedVisitPhaseRequestsInput] at hrequest
    | running remaining live =>
        have hrequestData :=
          (finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
            machine input.length remaining live).mp hrequest
        have hpositive := hrequestData.1
        have hneeds := hrequestData.2.1
        have hhead := hrequestData.2.2
        have hstep : verifier.step (.running remaining live)
            (some (.bit bit)) =
            advanceFiniteCachedVisitPhase machine H w base hbound remaining
              live (.bit bit) := by
          simp [verifier, finiteCachedVisitStreamingVerifier,
            finiteCachedVisitStreamingStep, hneeds, hhead]
        rw [hstep]
        cases hadvance : advanceFiniteCachedVisitPhase machine H w base hbound
            remaining live (.bit bit) with
        | running nextRemaining next =>
            have hzero : remaining.val ≠ 0 := Nat.ne_of_gt hpositive
            have hlast : remaining.val ≠ 1 := by
              intro hlast
              simp [advanceFiniteCachedVisitPhase, hlast] at hadvance
              cases hlocal : finiteLocalCachedFinalStep machine H w base
                  (.bit bit) live <;> simp [hlocal] at hadvance
            have hheadEq := advanceFiniteCachedVisitPhase_running_inputHead_eq
              machine hbound remaining nextRemaining live next (.bit bit)
                hzero hlast hadvance
            simpa [rank, finiteCachedVisitPhaseInputRank, hneeds] using hheadEq
        | completed nextFinal =>
            have hlast : remaining.val = 1 := by
              by_contra hlast
              have hzero : remaining.val ≠ 0 := Nat.ne_of_gt hpositive
              simp [advanceFiniteCachedVisitPhase, hzero, hlast] at hadvance
              cases hlocal : finiteLocalCachedStep machine H w base
                  (.bit bit) live <;> simp [hlocal] at hadvance
            have hheadEq := advanceFiniteCachedVisitPhase_completed_inputHead_eq
              machine hbound remaining live (.bit bit) nextFinal hlast hadvance
            simpa [rank, finiteCachedVisitPhaseInputRank, hneeds] using hheadEq
        | rejected failure =>
            have hstepRejected : verifier.step (.running remaining live)
                (some (.bit bit)) = .rejected failure :=
              hstep.trans hadvance
            have hhaltedRejected : verifier.halted
                (verifier.step (.running remaining live)
                  (some (.bit bit))) = true := by
              rw [hstepRejected]
              rfl
            have hterminal :=
              FiniteStreamingVerifier.ExactFreshTrace.eq_of_halted_start
                verifier (fun bit => .bit bit) htail hhaltedRejected
            have himpossible :
                (FiniteCachedVisitStreamingState.completed final :
                  verifier.State) = .rejected failure := by
              rw [← hstepRejected]
              exact hterminal.2.2
            cases himpossible
  have hsilentOrder : ∀ {tailSteps : Nat} {state : verifier.State}
      {tailAnswers : List Bool},
      verifier.halted state = false →
      verifier.requestsInput state = false →
      FiniteStreamingVerifier.ExactFreshTrace verifier
        (fun bit => .bit bit) tailSteps (verifier.step state none)
          tailAnswers (.completed final) →
      finiteInputVariableQueryOrder input.length
          (List.range' (rank state)
            (rank (.completed final) - rank state)) =
        finiteInputVariableQueryOrder input.length
          (List.range' (rank (verifier.step state none))
            (rank (.completed final) -
              rank (verifier.step state none))) := by
    intro tailSteps state tailAnswers hhalt hrequest htail
    cases state with
    | completed completed =>
        simp [verifier, finiteCachedVisitStreamingVerifier,
          finiteCachedVisitPhaseHalted] at hhalt
    | rejected failure =>
        simp [verifier, finiteCachedVisitStreamingVerifier,
          finiteCachedVisitPhaseHalted] at hhalt
    | running remaining live =>
        have hpositive : 0 < remaining.val := by
          have hzero : remaining.val ≠ 0 := by
            intro hzero
            simp [verifier, finiteCachedVisitStreamingVerifier,
              finiteCachedVisitPhaseHalted, hzero] at hhalt
          exact Nat.pos_of_ne_zero hzero
        by_cases hhead : live.inputHead.val < input.length
        · have hneedsFalse : cachedLocalStepNeedsUnread machine live = false := by
            cases hneeds : cachedLocalStepNeedsUnread machine live with
            | false => rfl
            | true =>
                have hrequestTrue : finiteCachedVisitPhaseRequestsInput machine
                    input.length (.running remaining live) = true :=
                  (finiteCachedVisitPhaseRequestsInput_running_eq_true_iff
                    machine input.length remaining live).mpr
                    ⟨hpositive, hneeds, hhead⟩
                change finiteCachedVisitPhaseRequestsInput machine input.length
                  (.running remaining live) = false at hrequest
                rw [hrequestTrue] at hrequest
                contradiction
          have hstep : verifier.step (.running remaining live) none =
              advanceFiniteCachedVisitPhase machine H w base hbound remaining
                live .rightEnd := by
            simp [verifier, finiteCachedVisitStreamingVerifier,
              finiteCachedVisitStreamingStep, hneedsFalse]
          rw [hstep]
          cases hadvance : advanceFiniteCachedVisitPhase machine H w base
              hbound remaining live .rightEnd with
          | running nextRemaining next =>
              have hzero : remaining.val ≠ 0 := Nat.ne_of_gt hpositive
              have hlast : remaining.val ≠ 1 := by
                intro hlast
                simp [advanceFiniteCachedVisitPhase, hlast] at hadvance
                cases hlocal : finiteLocalCachedFinalStep machine H w base
                    .rightEnd live <;> simp [hlocal] at hadvance
              have hheadEq :=
                advanceFiniteCachedVisitPhase_running_inputHead_eq machine
                  hbound remaining nextRemaining live next .rightEnd hzero
                    hlast hadvance
              simp [rank, finiteCachedVisitPhaseInputRank, hneedsFalse,
                hheadEq]
          | completed nextFinal =>
              have hlast : remaining.val = 1 := by
                by_contra hlast
                have hzero : remaining.val ≠ 0 := Nat.ne_of_gt hpositive
                simp [advanceFiniteCachedVisitPhase, hzero, hlast] at hadvance
                cases hlocal : finiteLocalCachedStep machine H w base
                    .rightEnd live <;> simp [hlocal] at hadvance
              have hheadEq :=
                advanceFiniteCachedVisitPhase_completed_inputHead_eq machine
                  hbound remaining live .rightEnd nextFinal hlast hadvance
              simp [rank, finiteCachedVisitPhaseInputRank, hneedsFalse,
                hheadEq]
          | rejected failure =>
              have hstepRejected : verifier.step (.running remaining live)
                  none = .rejected failure := hstep.trans hadvance
              have hhaltedRejected : verifier.halted
                  (verifier.step (.running remaining live) none) = true := by
                rw [hstepRejected]
                rfl
              have hterminal :=
                FiniteStreamingVerifier.ExactFreshTrace.eq_of_halted_start
                  verifier (fun bit => .bit bit) htail hhaltedRejected
              have himpossible :
                  (FiniteCachedVisitStreamingState.completed final :
                    verifier.State) = .rejected failure := by
                rw [← hstepRejected]
                exact hterminal.2.2
              cases himpossible
        · have hstart : input.length ≤ live.inputHead.val :=
            Nat.le_of_not_gt hhead
          have hstep : verifier.step (.running remaining live) none =
              advanceFiniteCachedVisitPhase machine H w base hbound remaining
                live .rightEnd := by
            simp [verifier, finiteCachedVisitStreamingVerifier,
              finiteCachedVisitStreamingStep, hhead]
          have hmono := advanceFiniteCachedVisitPhase_inputRank_mono machine
            hbound remaining live .rightEnd
          have hnext : input.length ≤
              rank (verifier.step (.running remaining live) none) := by
            rw [hstep]
            exact hstart.trans hmono
          have hstartRank : input.length ≤
              rank (.running remaining live) := by
            simpa [rank, finiteCachedVisitPhaseInputRank] using hstart
          calc
            finiteInputVariableQueryOrder input.length
                (List.range' (rank (.running remaining live))
                  (rank (.completed final) -
                    rank (.running remaining live))) = [] :=
              finiteInputVariableQueryOrder_range'_eq_nil_of_le hstartRank
            _ = finiteInputVariableQueryOrder input.length
                (List.range' (rank
                    (verifier.step (.running remaining live) none))
                  (rank (.completed final) - rank
                    (verifier.step (.running remaining live) none))) :=
              (finiteInputVariableQueryOrder_range'_eq_nil_of_le hnext).symm
  exact
    FiniteStreamingVerifier.ExactFreshTrace.toExactAdaptiveQueryOrder_of_rank
      verifier (fun bit => .bit bit) selector inputBits rank hsilentOrder
        hquerySelector hqueryRank trace hanswers

/-- A successful finite comparison run therefore exposes exactly its clipped
half-open input-head interval as adaptive coordinates. -/
theorem finiteCachedVisitCompleted_exactAdaptiveQueryOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {H w base : Nat}
    (hbound : base + w ≤ H + 1)
    (initialRemaining : Fin (H + 1))
    (initialLive : LocalReplayState
      (cachedInputMachine machine).State H w)
    (expected : FixedAlphaVisitEndpoint
      (cachedInputMachine machine).State H)
    (unreads : List ReadOnlySymbol)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hlength : initialRemaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input H w base
      unreads initialLive)
    (hcompleted :
      runFiniteCachedVisitStreamingWithUnreads machine input.length H w base
        hbound unreads (.running initialRemaining initialLive) =
          .completed final) :
    let verifier := finiteCachedVisitStreamingVerifier machine input.length
      H w base hbound initialRemaining initialLive expected
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder verifier
      (fun bit => .bit bit)
      (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) unreads.length
      (.running initialRemaining initialLive)
      (finiteInputVariableQueryOrder input.length
        (List.range' initialLive.inputHead.val
          (final.inputHead.val - initialLive.inputHead.val)))
      (.completed final) := by
  have htrace := finiteCachedVisitCompleted_exactFreshTrace machine input
    hbound initialRemaining initialLive expected unreads final hlength hagree
      hcompleted
  apply finiteCachedVisitExactFreshTrace_toExactAdaptiveQueryOrder machine input
    hbound initialRemaining initialLive expected final htrace
  rfl

/-- A concrete one-visit streaming certificate fixes the exact adaptive
coordinate trace while retaining its particular final slab. -/
theorem finiteCachedFixedAlphaVisit_exactAdaptiveQueryOrder_of_stepCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hcertificate : FiniteCachedFixedAlphaVisitStreamingStepCertificate
      machine input alpha block visit carried final) :
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length
        alpha block visit carried hentry)
      (fun bit => .bit bit)
      (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) visit.steps
      (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length
        alpha block visit carried hentry).start
      (fixedVisitFiniteFreshOrder input.length visit) (.completed final) := by
  rcases hcertificate with
    ⟨otherEntry, hagree, hstream, _hstate, hinput, _hwork⟩
  have hentryEq : otherEntry = hentry := Subsingleton.elim _ _
  subst otherEntry
  let initial := finiteCachedStateOfVisitEntry machine alpha block visit
    carried hentry
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps
  have hlength : (fixedAlphaVisitRemaining visit).val = unreads.length := by
    simp [unreads, fixedAlphaVisitRemaining]
  have hcoord := finiteCachedVisitCompleted_exactAdaptiveQueryOrder
    machine input
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (fixedAlphaVisitRemaining visit) initial visit.exit unreads final hlength
      hagree hstream
  have horder :
      finiteInputVariableQueryOrder input.length
          (List.range' initial.inputHead.val
            (final.inputHead.val - initial.inputHead.val)) =
        fixedVisitFiniteFreshOrder input.length visit := by
    unfold fixedVisitFiniteFreshOrder fixedVisitNaturalFreshOrder
    change finiteInputVariableQueryOrder input.length
        (List.range' visit.entry.inputHead.val
          (final.inputHead.val - visit.entry.inputHead.val)) = _
    rw [← hinput]
  rw [horder] at hcoord
  simpa [initial, unreads, finiteCachedFixedAlphaVisitStreamingVerifier,
    finiteCachedVisitStreamingVerifier, fixedAlphaVisitRemaining] using hcoord

/-- Semantic validity of one advertised visit fixes the complete adaptive
coordinate trace to `fixedVisitFiniteFreshOrder`. -/
theorem finiteCachedFixedAlphaVisit_exactAdaptiveQueryOrder_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (hvalid : FixedAlphaBlockVisitValid (cachedInputMachine machine) input
      alpha block visit carried) :
    ∃ final : FiniteLocalFinalState (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block),
      FiniteStreamingVerifier.ExactAdaptiveQueryOrder
        (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length
          alpha block visit carried hentry)
        (fun bit => .bit bit)
        (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) visit.steps
        (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length
          alpha block visit carried hentry).start
        (fixedVisitFiniteFreshOrder input.length visit) (.completed final) := by
  obtain ⟨final, otherEntry, hagree, hstream,
      _hstate, hinput, _hwork⟩ :=
    (exists_finiteCachedFixedAlphaVisitStreamingStepCertificate_iff
      machine input alpha block visit carried).mpr hvalid
  have hentryEq : otherEntry = hentry := Subsingleton.elim _ _
  subst otherEntry
  let initial := finiteCachedStateOfVisitEntry machine alpha block visit
    carried hentry
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps
  have hlength : (fixedAlphaVisitRemaining visit).val = unreads.length := by
    simp [unreads, fixedAlphaVisitRemaining]
  have hcoord := finiteCachedVisitCompleted_exactAdaptiveQueryOrder
    machine input
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    (fixedAlphaVisitRemaining visit) initial visit.exit unreads final hlength
      hagree hstream
  have horder :
      finiteInputVariableQueryOrder input.length
          (List.range' initial.inputHead.val
            (final.inputHead.val - initial.inputHead.val)) =
        fixedVisitFiniteFreshOrder input.length visit := by
    unfold fixedVisitFiniteFreshOrder fixedVisitNaturalFreshOrder
    change finiteInputVariableQueryOrder input.length
        (List.range' visit.entry.inputHead.val
          (final.inputHead.val - visit.entry.inputHead.val)) = _
    rw [← hinput]
  refine ⟨final, ?_⟩
  rw [horder] at hcoord
  simpa [initial, unreads, finiteCachedFixedAlphaVisitStreamingVerifier,
    finiteCachedVisitStreamingVerifier, fixedAlphaVisitRemaining] using hcoord

/-- Exact tail traces embed unchanged when one visit is prepended to the
list verifier. -/
theorem finiteCachedBlockVisitListExactAdaptiveQueryOrder_prepend
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (consInitial tailInitial : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hcons : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (htail : FixedAlphaBlockVisitEntriesInside alpha block rest)
    {steps : Nat}
    {state target : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) rest.length}
    {queries : List (Fin input.length)}
    (trace : FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block tailInitial rest htail)
      (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) steps state queries target) :
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block consInitial (first :: rest) hcons)
      (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) steps
      (prependFiniteCachedBlockVisitListState first rest state) queries
      (prependFiniteCachedBlockVisitListState first rest target) := by
  let source := finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
    input.length alpha block tailInitial rest htail
  let targetVerifier :=
    finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine input.length
      alpha block consInitial (first :: rest) hcons
  let selector : source.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let targetSelector : targetVerifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let embed : source.State → targetVerifier.State :=
    prependFiniteCachedBlockVisitListState first rest
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder source
    (fun bit => .bit bit) selector inputBits steps state queries target at trace
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder targetVerifier
    (fun bit => .bit bit) targetSelector inputBits steps (embed state) queries
      (embed target)
  have hhalted : ∀ state, source.halted state = false →
      targetVerifier.halted (embed state) = false := by
    intro current hcurrent
    change finiteCachedBlockVisitListHalted
        (prependFiniteCachedBlockVisitListState first rest current) = false
    rw [finiteCachedBlockVisitListHalted_prepend]
    exact hcurrent
  have hrequests : ∀ state, source.halted state = false →
      targetVerifier.requestsInput (embed state) =
        source.requestsInput state := by
    intro current _
    exact finiteCachedBlockVisitListRequestsInput_prepend machine input.length
      first rest current
  have hselector : ∀ state, source.halted state = false →
      targetSelector (embed state) = selector state := by
    intro current _
    exact finiteCachedBlockVisitListAdaptiveQueryIndex?_prepend machine
      input.length first rest current
  have hstep : ∀ state supplied, source.halted state = false →
      targetVerifier.step (embed state) supplied =
        embed (source.step state supplied) := by
    intro current supplied _
    exact finiteCachedBlockVisitListStreamingStep_prepend machine input.length
      alpha block first rest hcons htail current supplied
  have htargetHalted : targetVerifier.halted (embed target) = true := by
    change finiteCachedBlockVisitListHalted
        (prependFiniteCachedBlockVisitListState first rest target) = true
    rw [finiteCachedBlockVisitListHalted_prepend]
    exact trace.target_halted source (fun bit => .bit bit) selector inputBits
  have terminal : FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      targetVerifier (fun bit => .bit bit) targetSelector inputBits 0
      (embed target) [] (embed target) :=
    .halted (embed target) htargetHalted
  have mapped := trace.map_append source targetVerifier
    (fun bit => .bit bit) selector targetSelector inputBits embed hhalted
      hrequests hselector hstep terminal
  simpa using mapped

/-- Lift the exact trace of the head visit under a fixed list cursor and
splice in a continuation beginning at its locally completed phase. -/
theorem finiteCachedFixedAlphaVisitExactAdaptiveQueryOrder_lift_append
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      first.entry.workHead.val)
    (cursor : Fin (first :: rest).length)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (headTrace : FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length alpha
        block first initialSlab hentry)
      (fun bit => .bit bit)
      (finiteCachedVisitAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) first.steps
      (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length alpha
        block first initialSlab hentry).start
      (fixedVisitFiniteFreshOrder input.length first) (.completed final))
    {tailSteps : Nat} {tailQueries : List (Fin input.length)}
    {target : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) (first :: rest).length}
    (continuation : FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block initialSlab (first :: rest) hentries)
      (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) tailSteps
      (.active cursor (.completed final)) tailQueries target) :
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block initialSlab (first :: rest) hentries)
      (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) (first.steps + tailSteps)
      (.active cursor
        (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length
          alpha block first initialSlab hentry).start)
      (fixedVisitFiniteFreshOrder input.length first ++ tailQueries) target := by
  let source := finiteCachedFixedAlphaVisitStreamingVerifier machine
    input.length alpha block first initialSlab hentry
  let targetVerifier :=
    finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine input.length
      alpha block initialSlab (first :: rest) hentries
  let sourceSelector : source.State → Option (Fin input.length) :=
    finiteCachedVisitAdaptiveQueryIndex? machine input.length
  let targetSelector : targetVerifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let embed : source.State → targetVerifier.State :=
    liftFiniteCachedBlockVisitPhase cursor
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder source
    (fun bit => .bit bit) sourceSelector inputBits first.steps source.start
      (fixedVisitFiniteFreshOrder input.length first) (.completed final)
        at headTrace
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder targetVerifier
    (fun bit => .bit bit) targetSelector inputBits tailSteps
      (embed (.completed final)) tailQueries target at continuation
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder targetVerifier
    (fun bit => .bit bit) targetSelector inputBits (first.steps + tailSteps)
      (embed source.start)
      (fixedVisitFiniteFreshOrder input.length first ++ tailQueries) target
  have hhalted : ∀ state, source.halted state = false →
      targetVerifier.halted (embed state) = false := by
    intro current hcurrent
    cases current with
    | running remaining live => rfl
    | completed completed =>
        simp [source, finiteCachedFixedAlphaVisitStreamingVerifier,
          finiteCachedVisitStreamingVerifier, finiteCachedVisitPhaseHalted]
          at hcurrent
    | rejected failure =>
        simp [source, finiteCachedFixedAlphaVisitStreamingVerifier,
          finiteCachedVisitStreamingVerifier, finiteCachedVisitPhaseHalted]
          at hcurrent
  have hrequests : ∀ state, source.halted state = false →
      targetVerifier.requestsInput (embed state) = source.requestsInput state := by
    intro current _
    cases current <;> rfl
  have hselector : ∀ state, source.halted state = false →
      targetSelector (embed state) = sourceSelector state := by
    intro current _
    cases current <;> rfl
  have hstep : ∀ state supplied, source.halted state = false →
      targetVerifier.step (embed state) supplied =
        embed (source.step state supplied) := by
    intro current supplied hcurrent
    cases current with
    | running remaining live => rfl
    | completed completed =>
        simp [source, finiteCachedFixedAlphaVisitStreamingVerifier,
          finiteCachedVisitStreamingVerifier, finiteCachedVisitPhaseHalted]
          at hcurrent
    | rejected failure =>
        simp [source, finiteCachedFixedAlphaVisitStreamingVerifier,
          finiteCachedVisitStreamingVerifier, finiteCachedVisitPhaseHalted]
          at hcurrent
  exact headTrace.map_append source targetVerifier (fun bit => .bit bit)
    sourceSelector targetSelector inputBits embed hhalted hrequests hselector
      hstep continuation

/-- The schedule-advertised coordinate order of one fixed-block visit list. -/
def finiteCachedBlockVisitListAdvertisedQueryOrder
    {State : Type} {T : Nat} (n : Nat)
    (visits : List (FixedAlphaBlockVisit State T)) : List (Fin n) :=
  visits.flatMap (fixedVisitFiniteFreshOrder n)

/-- A recursively threaded finite streaming certificate determines the exact
coordinate trace of the entire fixed-block visit list. -/
theorem finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hcertificate : FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
      machine input alpha block initialSlab visits) :
    ∃ finalSlab : WorkSlab (advertisedBlockWidth alpha.offsets block),
      FiniteStreamingVerifier.ExactAdaptiveQueryOrder
        (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
          input.length alpha block initialSlab visits hentries)
        (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel visits)
        (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
          input.length alpha block initialSlab visits hentries).start
        (finiteCachedBlockVisitListAdvertisedQueryOrder input.length visits)
        (.completed finalSlab) := by
  induction visits generalizing initialSlab with
  | nil =>
      refine ⟨initialSlab, ?_⟩
      change FiniteStreamingVerifier.ExactAdaptiveQueryOrder
        (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
          input.length alpha block initialSlab [] hentries)
        (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) 0 (.completed initialSlab) []
          (.completed initialSlab)
      apply FiniteStreamingVerifier.ExactAdaptiveQueryOrder.halted
      rfl
  | cons first rest ih =>
      rcases hcertificate with ⟨firstFinal, hfirst, htail⟩
      let tailEntries : FixedAlphaBlockVisitEntriesInside alpha block rest :=
        fun visit hmem => hentries visit (by simp [hmem])
      obtain ⟨finalSlab, tailTrace⟩ :=
        ih firstFinal.workSlab tailEntries htail
      let consVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab (first :: rest) hentries
      let tailVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block firstFinal.workSlab rest tailEntries
      let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
      let firstEntry : WorkCellInSlab
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockWidth alpha.offsets block)
          first.entry.workHead.val := hentries first (by simp)
      have headTrace :=
        finiteCachedFixedAlphaVisit_exactAdaptiveQueryOrder_of_stepCertificate
          machine input alpha block first initialSlab firstEntry firstFinal
            hfirst
      have tailMapped :=
        finiteCachedBlockVisitListExactAdaptiveQueryOrder_prepend machine input
          alpha block first rest initialSlab firstFinal.workSlab hentries
            tailEntries tailTrace
      rcases hfirst with
        ⟨_firstEntry, _firstAgree, _firstStream,
          firstState, firstInput, firstWork⟩
      have hfirstAccept : @finiteCachedVisitPhaseAccept
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block) first.exit
          (.completed firstFinal) = true :=
        (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block) first.exit firstFinal).2
            ⟨firstState, firstInput, firstWork⟩
      have hboundaryStep : consVerifier.step
          (.active cursor (.completed firstFinal)) none =
        prependFiniteCachedBlockVisitListState first rest
          tailVerifier.start := by
        cases rest with
        | nil =>
            simp [consVerifier, tailVerifier, cursor,
              finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
              finiteCachedBlockVisitListStart,
              finiteCachedBlockVisitListStreamingStep,
              prependFiniteCachedBlockVisitListState, hfirstAccept]
        | cons second remaining =>
            simp [consVerifier, tailVerifier, cursor,
              finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
              finiteCachedBlockVisitListStart,
              finiteCachedBlockVisitListStreamingStep, hfirstAccept,
              finiteCachedBlockVisitListActiveState,
              prependFiniteCachedBlockVisitListState]
      have boundaryAndTail :
          FiniteStreamingVerifier.ExactAdaptiveQueryOrder consVerifier
            (fun bit => .bit bit)
            (finiteCachedBlockVisitListAdaptiveQueryIndex? machine
              input.length)
            (fun index => input.get index)
            (finiteCachedBlockVisitListFuel rest + 1)
            (.active cursor (.completed firstFinal))
            (finiteCachedBlockVisitListAdvertisedQueryOrder input.length rest)
            (.completed finalSlab) := by
        apply FiniteStreamingVerifier.ExactAdaptiveQueryOrder.silent
          (by rfl) (by rfl)
        rw [hboundaryStep]
        simpa [consVerifier, tailVerifier] using tailMapped
      have combined :=
        finiteCachedFixedAlphaVisitExactAdaptiveQueryOrder_lift_append
          machine input alpha block first rest initialSlab hentries firstEntry
            cursor firstFinal headTrace boundaryAndTail
      have hfuel : finiteCachedBlockVisitListFuel (first :: rest) =
          first.steps + (finiteCachedBlockVisitListFuel rest + 1) := by
        simp [finiteCachedBlockVisitListFuel,
          fixedAlphaBlockVisitsTotalSteps]
        omega
      have hstart : consVerifier.start =
          .active cursor
            (finiteCachedFixedAlphaVisitStreamingVerifier machine input.length
              alpha block first initialSlab firstEntry).start := by
        simp [consVerifier, cursor,
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListStart,
          finiteCachedBlockVisitListActiveState,
          finiteCachedFixedAlphaVisitStreamingVerifier,
          finiteCachedVisitStreamingVerifier]
      refine ⟨finalSlab, ?_⟩
      change FiniteStreamingVerifier.ExactAdaptiveQueryOrder consVerifier
        (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel (first :: rest)) consVerifier.start
        (finiteCachedBlockVisitListAdvertisedQueryOrder input.length
          (first :: rest)) (.completed finalSlab)
      rw [hfuel, hstart]
      simpa [finiteCachedBlockVisitListAdvertisedQueryOrder] using combined

/-- Accepted replay fixes the executable block-list compiler's complete
query trace to the advertised flat-map order, with no residual premise. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_queryTrace_eq_advertised_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
      initialSlab visits hentries).queryTrace (fun index => input.get index) =
        finiteCachedBlockVisitListAdvertisedQueryOrder input.length visits := by
  have hcertificate :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block initialSlab visits).mpr haccepted
  obtain ⟨finalSlab, trace⟩ :=
    finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
      machine input alpha block initialSlab visits hentries hcertificate
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  have hqueryTrace := trace.compileAdaptive_queryTrace_eq verifier
    (fun bit => .bit bit) .rightEnd selector inputBits le_rfl
  simpa [compileAdaptiveFiniteCachedFixedAlphaBlockVisitList, verifier,
    selector, inputBits] using hqueryTrace

/-- The remaining coordinate-identification statement for one accepted block:
every exact completed execution must expose precisely the flat-map of the
advertised half-open fresh intervals. -/
def FiniteCachedBlockVisitListExactTraceMatchesAdvertisedOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) : Prop :=
  ∀ (steps : Nat) (queries : List (Fin input.length))
      (final : WorkSlab (advertisedBlockWidth alpha.offsets block)),
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder
        (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
          input.length alpha block initialSlab visits hentries)
        (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) steps
        (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
          input.length alpha block initialSlab visits hentries).start
        queries (.completed final) →
      queries = finiteCachedBlockVisitListAdvertisedQueryOrder
        input.length visits

/-- The coordinate-identification residual is unconditional for the empty
block list. -/
theorem finiteCachedBlockVisitListExactTraceMatchesAdvertisedOrder_nil
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block []) :
    FiniteCachedBlockVisitListExactTraceMatchesAdvertisedOrder machine input
      alpha block initialSlab [] hentries := by
  intro steps queries final htrace
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab [] hentries
  have hhalted : verifier.halted verifier.start = true := by
    rfl
  have hnil :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.queries_eq_nil_of_halted
      verifier (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) htrace hhalted
  simpa [finiteCachedBlockVisitListAdvertisedQueryOrder] using hnil

/-- Accepted replay discharges the former coordinate-identification residual:
the constructed advertised trace and any other exact trace start in the same
deterministic verifier state, hence expose the same coordinates. -/
theorem finiteCachedBlockVisitListExactTraceMatchesAdvertisedOrder_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    FiniteCachedBlockVisitListExactTraceMatchesAdvertisedOrder machine input
      alpha block initialSlab visits hentries := by
  have hcertificate :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block initialSlab visits).mpr haccepted
  obtain ⟨advertisedFinal, advertisedTrace⟩ :=
    finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
      machine input alpha block initialSlab visits hentries hcertificate
  intro steps queries final trace
  exact
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.queries_eq_of_same_start
      _ _ _ _ trace advertisedTrace

/-- Accepted replay produces a coordinate-exact certificate for the actual
compiled query trace of one whole block.  Thus the remaining block-level
master-order issue is only identification of this trace with the advertised
flat-map order; it is no longer mixed with adaptive execution semantics. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_queryTrace_exact_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    ∃ final : WorkSlab (advertisedBlockWidth alpha.offsets block),
      ∃ steps,
        steps ≤ finiteCachedBlockVisitListFuel visits ∧
          FiniteStreamingVerifier.ExactAdaptiveQueryOrder
            (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
              input.length alpha block initialSlab visits hentries)
            (fun bit => .bit bit)
            (finiteCachedBlockVisitListAdaptiveQueryIndex? machine
              input.length)
            (fun index => input.get index) steps
            (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
              input.length alpha block initialSlab visits hentries).start
            ((compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine
              alpha block initialSlab visits hentries).queryTrace
                (fun index => input.get index))
            (.completed final) := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  have hcertificate :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block initialSlab visits).mpr haccepted
  obtain ⟨final, hcore⟩ :=
    finiteCachedBlockVisitList_inputDrivenCore_completed_of_certificate
      machine input alpha block initialSlab visits hentries hcertificate
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedBlockVisitListFuel visits) verifier.start =
        .completed final at hcore
  have htotal : ∀ state, verifier.requestsInput state = true →
      ∃ index, selector state = some index := by
    intro state hrequest
    exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
      machine input.length state hrequest
  have hhalted : verifier.halted
      (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
        (finiteCachedBlockVisitListFuel visits) verifier.start) = true := by
    rw [hcore]
    rfl
  obtain ⟨steps, queries, hsteps, htrace⟩ :=
    FiniteStreamingVerifier.exists_exactAdaptiveQueryOrder_of_inputDrivenCore_halted
      verifier (fun bit => .bit bit) selector inputBits htotal
        (finiteCachedBlockVisitListFuel visits) verifier.start hhalted
  rw [hcore] at htrace
  have hqueryTrace :
      (verifier.compileAdaptive (finiteCachedBlockVisitListFuel visits)
        input.length (fun bit => .bit bit) .rightEnd selector).queryTrace
          inputBits = queries :=
    htrace.compileAdaptive_queryTrace_eq verifier (fun bit => .bit bit)
      .rightEnd selector inputBits hsteps
  refine ⟨final, steps, hsteps, ?_⟩
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder verifier
    (fun bit => .bit bit) selector inputBits steps verifier.start
      ((verifier.compileAdaptive (finiteCachedBlockVisitListFuel visits)
        input.length (fun bit => .bit bit) .rightEnd selector).queryTrace
          inputBits) (.completed final)
  rw [hqueryTrace]
  exact htrace

/-- Accepted block replay unconditionally discharges the guarded compiler's
`follows-master` premise on the canonical Boolean input. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_executionQueriesFollowAdvertisedOrder_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    LayeredQueryProgram.ExecutionQueriesFollowMaster
      (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
        initialSlab visits hentries)
      (finiteCachedBlockVisitListAdvertisedQueryOrder input.length visits)
      (fun index => input.get index) := by
  exact LayeredQueryProgram.executionQueriesFollowMaster_of_queryTrace_eq
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
      initialSlab visits hentries)
    (finiteCachedBlockVisitListAdvertisedQueryOrder input.length visits)
    (fun index => input.get index)
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_queryTrace_eq_advertised_of_replayAccepted
      machine input alpha block initialSlab visits hentries haccepted)

/-- Stable filtering of advertised crossing segments for one work block is
literally the chronological fresh-coordinate order of that block's visits. -/
theorem timedAlphaCrossingScheduleSegments_blockFreshQueries_eq
    {State : Type} {T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (block : Fin (T / b + 1)) :
    ((timedAlphaCrossingScheduleSegments scheduled hmonotone).filter
        (fun segment => segment.workBlock == block)).flatMap
          CrossingScheduleSegment.freshQueries =
      (timedAlphaBlockVisits block scheduled).flatMap
        fixedVisitNaturalFreshOrder := by
  induction scheduled with
  | nil => rfl
  | cons first rest ih =>
      let htail : TimedAlphaScheduledVisitsInputMonotone rest := by
        intro later hlater
        exact hmonotone later (by simp [hlater])
      have hih := ih htail
      by_cases hblock : first.block = block
      · simp [timedAlphaCrossingScheduleSegments,
          timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
          timedAlphaScheduledVisitCrossingSegment,
          CrossingScheduleSegment.freshQueries,
          fixedVisitNaturalFreshOrder, hblock, hih]
      · simp [timedAlphaCrossingScheduleSegments,
          timedAlphaBlockVisits, timedAlphaScheduledVisitsForBlock,
          timedAlphaScheduledVisitCrossingSegment,
          hblock, hih]

/-- The schedule's natural-number grouped order is exactly the outer
compiler's block order followed by the chronological visits in each block. -/
theorem timedAlphaStableGroupedQueryOrder_eq_blockVisits
    {State : Type} {T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    timedAlphaStableGroupedQueryOrder scheduled hmonotone =
      (List.finRange (T / b + 1)).flatMap (fun block =>
        (timedAlphaBlockVisits block scheduled).flatMap
          fixedVisitNaturalFreshOrder) := by
  unfold timedAlphaStableGroupedQueryOrder
    stableGroupedCrossingScheduleInputOrder
    stableGroupedCrossingScheduleSegments
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro block _
  exact timedAlphaCrossingScheduleSegments_blockFreshQueries_eq
    scheduled hmonotone block

/-- After clipping natural input positions to `Fin n`, the static schedule
master order is precisely the concatenation of the per-block advertised
orders used by the executable outer compiler. -/
theorem finiteCachedTimedAlphaScheduleMasterQueryOrder_eq_blockVisits
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    finiteCachedTimedAlphaScheduleMasterQueryOrder
        (n := n) scheduled hmonotone =
      (List.finRange (T / b + 1)).flatMap (fun block =>
        finiteCachedBlockVisitListAdvertisedQueryOrder n
          (timedAlphaBlockVisits block scheduled)) := by
  unfold finiteCachedTimedAlphaScheduleMasterQueryOrder
    timedAlphaFiniteInputVariableQueryOrder
  rw [timedAlphaStableGroupedQueryOrder_eq_blockVisits scheduled hmonotone]
  simp only [finiteInputVariableQueryOrder, List.filterMap_flatMap,
    finiteCachedBlockVisitListAdvertisedQueryOrder]
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
