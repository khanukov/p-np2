import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.LayeredQueryProgram

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Collapsing input-free microsteps between fixed input queries

The cached-input simulation may perform many `Stay` transitions without
consulting a fresh input bit.  A standard ordered branching program has one
transition per hardwired variable.  This file gives the finite, width-exact
bridge between those views.

A `FiniteStreamingVerifier` has a finite live state, may halt, and otherwise
either requests the next fresh bit or performs an input-free microstep.  With
a hard fuel bound `H`, `silentClosure` runs all currently available silent
microsteps.  `compileFixedOrder` then queries every variable in one fixed
order; a query is consumed only when the verifier is waiting for it, and is a
dummy query otherwise.  The final output performs the remaining silent
closure.  Thus silent timing never appears in the branching-program layer
schedule and the live width is exactly `(H + 1) * |State|`.
-/

/-- A deterministic finite-state verifier which reads a one-way stream of
fresh Boolean symbols, interspersed with input-free microsteps. -/
structure FiniteStreamingVerifier (Symbol : Type) where
  State : Type
  stateFintype : Fintype State
  start : State
  halted : State → Bool
  requestsInput : State → Bool
  step : State → Option Symbol → State
  accept : State → Bool

namespace FiniteStreamingVerifier

variable {Symbol : Type}

instance (verifier : FiniteStreamingVerifier Symbol) :
    Fintype verifier.State := verifier.stateFintype

/-- Run input-free steps until fuel is exhausted, the verifier halts, or it
requests the next fresh input symbol.  The second result component is the
unspent fuel. -/
def silentClosureCore (verifier : FiniteStreamingVerifier Symbol) :
    Nat → verifier.State → verifier.State × Nat
  | 0, state => (state, 0)
  | fuel + 1, state =>
      if verifier.halted state || verifier.requestsInput state then
        (state, fuel + 1)
      else
        silentClosureCore verifier fuel (verifier.step state none)

/-- Silent closure never creates fuel. -/
theorem silentClosureCore_remaining_le (verifier : FiniteStreamingVerifier Symbol)
    (fuel : Nat) (state : verifier.State) :
    (verifier.silentClosureCore fuel state).2 ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [silentClosureCore]
  | succ fuel ih =>
      simp only [silentClosureCore]
      split
      · exact le_rfl
      · exact (ih _).trans (Nat.le_succ fuel)

/-- On return, closure has either spent all fuel or is stopped at a halt or
fresh-input request. -/
theorem silentClosureCore_stopped (verifier : FiniteStreamingVerifier Symbol)
    (fuel : Nat) (state : verifier.State) :
    (verifier.silentClosureCore fuel state).2 = 0 ∨
      verifier.halted (verifier.silentClosureCore fuel state).1 = true ∨
      verifier.requestsInput
        (verifier.silentClosureCore fuel state).1 = true := by
  induction fuel generalizing state with
  | zero => simp [silentClosureCore]
  | succ fuel ih =>
      simp only [silentClosureCore]
      by_cases hstop :
          (verifier.halted state || verifier.requestsInput state) = true
      · rw [if_pos hstop]
        right
        simpa only [Bool.or_eq_true] using hstop
      · rw [if_neg hstop]
        exact ih (verifier.step state none)

/-- Live compiler state: verifier state together with remaining microstep
fuel. -/
abbrev FueledState (verifier : FiniteStreamingVerifier Symbol) (H : Nat) :=
  verifier.State × Fin (H + 1)

/-- Width of the fueled live carrier. -/
@[simp]
theorem card_fueledState (verifier : FiniteStreamingVerifier Symbol) (H : Nat) :
    Fintype.card (verifier.FueledState H) =
      Fintype.card verifier.State * (H + 1) := by
  simp [FueledState]

/-- Repackage silent closure at a fixed global horizon. -/
def silentClosure (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (state : verifier.FueledState H) : verifier.FueledState H :=
  let closed := verifier.silentClosureCore state.2.val state.1
  (closed.1, ⟨closed.2, by
    have hle := verifier.silentClosureCore_remaining_le state.2.val state.1
    exact lt_of_le_of_lt hle state.2.isLt⟩)

/-- Fixed-horizon closure also stops exactly at zero fuel, halt, or request. -/
theorem silentClosure_stopped (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (state : verifier.FueledState H) :
    (verifier.silentClosure state).2.val = 0 ∨
      verifier.halted (verifier.silentClosure state).1 = true ∨
      verifier.requestsInput (verifier.silentClosure state).1 = true := by
  exact verifier.silentClosureCore_stopped state.2.val state.1

/-- Spend one unit of a bounded fuel counter. -/
def spendOne {H : Nat} (remaining : Fin (H + 1)) : Fin (H + 1) :=
  ⟨remaining.val - 1,
    lt_of_le_of_lt (Nat.sub_le remaining.val 1) remaining.isLt⟩

/-- Process one hardwired branching-program query.  First close all silent
steps.  Consume the supplied bit exactly when positive fuel remains and the
verifier is waiting for fresh input; otherwise the query is a dummy. -/
def consumeQuery (verifier : FiniteStreamingVerifier Symbol) {H : Nat}
    (encode : Bool → Symbol)
    (state : verifier.FueledState H) (answer : Bool) :
    verifier.FueledState H :=
  let closed := verifier.silentClosure state
  if 0 < closed.2.val && !verifier.halted closed.1 &&
      verifier.requestsInput closed.1 then
    (verifier.step closed.1 (some (encode answer)), spendOne closed.2)
  else
    closed

/-- Initial fueled state. -/
def initialFueledState (verifier : FiniteStreamingVerifier Symbol) (H : Nat) :
    verifier.FueledState H :=
  (verifier.start, ⟨H, Nat.lt_succ_self H⟩)

/-- Execute the hardwired query list in bulk.  This is the streaming
semantics to which the compiled branching program is compared. -/
def runFixedOrder (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool → Symbol) {n : Nat}
    (order : Fin n → Fin n) (input : Fin n → Bool) :
    verifier.FueledState H :=
  (List.ofFn fun position => input (order position)).foldl
    (verifier.consumeQuery encode) (verifier.initialFueledState H)

/-- After all genuine variables have been queried, every further requested
symbol is the fixed end-of-input symbol.  This terminal closure therefore
uses no input variable and runs until halt or fuel exhaustion. -/
def terminalClosureCore (verifier : FiniteStreamingVerifier Symbol)
    (endSymbol : Symbol) : Nat → verifier.State → verifier.State
  | 0, state => state
  | fuel + 1, state =>
      if verifier.halted state then
        state
      else
        terminalClosureCore verifier endSymbol fuel
          (verifier.step state
            (if verifier.requestsInput state then some endSymbol else none))

/-- Finish a fueled computation after the finite Boolean input has ended. -/
def finishWithEndSymbol (verifier : FiniteStreamingVerifier Symbol)
    {H : Nat} (endSymbol : Symbol) (state : verifier.FueledState H) :
    verifier.State :=
  verifier.terminalClosureCore endSymbol state.2.val state.1

/-- Compile silent microsteps away.  Every layer queries its hardwired
variable; queries after the verifier has halted (or after its own advertised
input endpoint) are harmless dummies. -/
def compileFixedOrder (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) : LayeredQueryProgram n n where
  State := verifier.FueledState H
  stateFintype := inferInstance
  start := verifier.initialFueledState H
  query? := fun layer _ => some (order layer)
  next := fun _ state answer =>
    match answer with
    | none => state
    | some bit => verifier.consumeQuery encode state bit
  output := fun state =>
    verifier.accept (verifier.finishWithEndSymbol endSymbol state)

/-- The compiled program has exactly the requested fixed order. -/
theorem compileFixedOrder_hasFixedQueryOrder
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) :
    (verifier.compileFixedOrder H n encode endSymbol order).HasFixedQueryOrder
      (fun layer => some (order layer)) := by
  intro layer state
  rfl

/-- Every execution has exactly the advertised query trace; silent timing,
answers, and verifier state cannot change it. -/
theorem compileFixedOrder_queryTrace
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) (input : Fin n → Bool) :
    (verifier.compileFixedOrder H n encode endSymbol order).queryTrace input =
      List.ofFn order := by
  rw [LayeredQueryProgram.queryTrace,
    LayeredQueryProgram.executePrefix_trace_eq_fixedQueryOrderPrefix
      (verifier.compileFixedOrder H n encode endSymbol order) input
      (fun layer => some (order layer))
      (verifier.compileFixedOrder_hasFixedQueryOrder
        H n encode endSymbol order)]
  unfold LayeredQueryProgram.fixedQueryOrderPrefix
  have hcast : (fun i : Fin n =>
      (some (order (Fin.castLE le_rfl i)) : Option (Fin n))) =
      fun i => some (order i) := by
    funext i
    rfl
  rw [hcast]
  have hofFn :
      (List.ofFn fun i => some (order i)) =
        (List.ofFn order).map some := by
    rw [List.map_ofFn]
    congr 1
  rw [hofFn]
  induction List.ofFn order with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- A duplicate-free hardwired order gives a read-once program. -/
theorem compileFixedOrder_isReadOnce
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) (hnodup : (List.ofFn order).Nodup) :
    (verifier.compileFixedOrder H n encode endSymbol order).IsReadOnce := by
  apply LayeredQueryProgram.isReadOnce_of_fixedQueryOrder_nodup
    (order := fun layer => some (order layer))
  · exact verifier.compileFixedOrder_hasFixedQueryOrder
      H n encode endSymbol order
  · have hofFn :
        (List.ofFn fun layer => some (order layer)) =
          (List.ofFn order).map some := by
      rw [List.map_ofFn]
      congr 1
    rw [hofFn]
    have hfilter : ∀ xs : List (Fin n),
        (xs.map some).filterMap id = xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons head tail ih => simp [ih]
    rw [hfilter]
    exact hnodup

/-- In particular, the compiled verifier is oblivious. -/
theorem compileFixedOrder_isOblivious
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) :
    (verifier.compileFixedOrder H n encode endSymbol order).IsOblivious := by
  exact ⟨fun layer => some (order layer),
    verifier.compileFixedOrder_hasFixedQueryOrder
      H n encode endSymbol order⟩

/-- Silent collapse preserves the exact live width: no silent-time layer or
closure history is stored. -/
@[simp]
theorem compileFixedOrder_width
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) :
    (verifier.compileFixedOrder H n encode endSymbol order).width =
      Fintype.card verifier.State * (H + 1) := by
  simp [compileFixedOrder, LayeredQueryProgram.width]

/-- State component of a compiled prefix equals the corresponding bulk fold
over the prefix of the fixed input order. -/
theorem compileFixedOrder_executePrefix_state
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) (input : Fin n → Bool)
    (k : Nat) (hk : k ≤ n) :
    ((verifier.compileFixedOrder H n encode endSymbol order).executePrefix
      input k hk).1 =
      (List.ofFn fun i : Fin k =>
        input (order (Fin.castLE hk i))).foldl
          (verifier.consumeQuery encode)
            (verifier.initialFueledState H) := by
  induction k with
  | zero =>
      simp [LayeredQueryProgram.executePrefix, compileFixedOrder,
        initialFueledState]
  | succ k ih =>
      simp only [LayeredQueryProgram.executePrefix]
      rw [ih (by omega)]
      simp only [compileFixedOrder, Option.map_some]
      rw [List.ofFn_succ_last, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hprefix :
          (fun i : Fin k => input (order (Fin.castLE (by omega) i))) =
            (fun i : Fin k =>
              input (order (Fin.castLE hk i.castSucc))) := by
        funext i
        congr 3
      rw [hprefix]
      have hlast : (⟨k, by omega⟩ : Fin n) =
          Fin.castLE hk (Fin.last k) := Fin.ext rfl
      rw [hlast]

/-- The final compiled state is exactly the streaming fixed-order fold. -/
theorem compileFixedOrder_finalState_eq_runFixedOrder
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) (input : Fin n → Bool) :
    (verifier.compileFixedOrder H n encode endSymbol order).finalState input =
      verifier.runFixedOrder H encode order input := by
  simpa [LayeredQueryProgram.finalState, runFixedOrder] using
    (verifier.compileFixedOrder_executePrefix_state
      H n encode endSymbol order input n le_rfl)

/-- Exact semantic equation for the compiled ordered branching program. -/
theorem compileFixedOrder_eval
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (order : Fin n → Fin n) (input : Fin n → Bool) :
    (verifier.compileFixedOrder H n encode endSymbol order).eval input =
      verifier.accept
        (verifier.finishWithEndSymbol endSymbol
          (verifier.runFixedOrder H encode order input)) := by
  rw [LayeredQueryProgram.eval,
    verifier.compileFixedOrder_finalState_eq_runFixedOrder]
  rfl

/-- Turn a length-`n` list into the layer-indexed order expected by the
compiler.  This is the direct bridge from the executable timed-alpha order
builder, whose natural output is a list. -/
def fixedOrderFunctionOfList {n : Nat} (order : List (Fin n))
    (hlength : order.length = n) : Fin n → Fin n :=
  fun position => order.get (Fin.cast hlength.symm position)

/-- Converting a length-indexed list to a function and back loses no entry. -/
theorem ofFn_fixedOrderFunctionOfList {n : Nat} (order : List (Fin n))
    (hlength : order.length = n) :
    List.ofFn (fixedOrderFunctionOfList order hlength) = order := by
  apply List.ext_getElem
  · simp [hlength]
  · intro i hiLeft hiRight
    simp [fixedOrderFunctionOfList]

/-- Compile a duplicate-free list order directly. -/
def compileFixedOrderList (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    {n : Nat} (order : List (Fin n)) (hlength : order.length = n) :
    LayeredQueryProgram n n :=
  verifier.compileFixedOrder H n encode endSymbol
    (fixedOrderFunctionOfList order hlength)

/-- The list-facing compiler exposes exactly that list as its query trace. -/
theorem compileFixedOrderList_queryTrace
    (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    {n : Nat} (order : List (Fin n)) (hlength : order.length = n)
    (input : Fin n → Bool) :
    (verifier.compileFixedOrderList H encode endSymbol order hlength).queryTrace
      input = order := by
  rw [compileFixedOrderList,
    verifier.compileFixedOrder_queryTrace H n encode endSymbol]
  exact ofFn_fixedOrderFunctionOfList order hlength

/-- List-ordered compilation is read-once. -/
theorem compileFixedOrderList_isReadOnce
    (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    {n : Nat} (order : List (Fin n)) (hlength : order.length = n)
    (hnodup : order.Nodup) :
    (verifier.compileFixedOrderList H encode endSymbol order hlength).IsReadOnce := by
  apply verifier.compileFixedOrder_isReadOnce
  simpa [ofFn_fixedOrderFunctionOfList order hlength] using hnodup

/-- List-ordered compilation has the same exact width. -/
@[simp]
theorem compileFixedOrderList_width
    (verifier : FiniteStreamingVerifier Symbol) (H : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    {n : Nat} (order : List (Fin n)) (hlength : order.length = n) :
    (verifier.compileFixedOrderList H encode endSymbol order hlength).width =
      Fintype.card verifier.State * (H + 1) := by
  exact verifier.compileFixedOrder_width H n encode endSymbol
    (fixedOrderFunctionOfList order hlength)

end FiniteStreamingVerifier

end OneTapeMagnification
end Frontier
end Pnp4
