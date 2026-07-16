import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite layered query programs

This is the small branching-program semantics needed by the fixed-alpha
simulation.  A layer may either query an input coordinate or perform an
input-free transition.  The next query is allowed to depend on the current
state, so the base model includes adaptive programs; `HasFixedQueryOrder`
isolates the oblivious case used by Viola's individual components.

Width is the cardinality of the finite live-state carrier.  Layer numbers and
hardwired advice are external to that carrier.
-/

/-- A deterministic finite-state program with `L` ordered layers over `n`
Boolean input variables. -/
structure LayeredQueryProgram (n L : Nat) where
  State : Type
  stateFintype : Fintype State
  start : State
  query? : Fin L → State → Option (Fin n)
  next : Fin L → State → Option Bool → State
  output : State → Bool

namespace LayeredQueryProgram

/-- Execute the first `k` layers, returning both the live state and the
chronological list of queried coordinates. -/
def executePrefix {n L : Nat} (program : LayeredQueryProgram n L)
    (input : Fin n → Bool) :
    (k : Nat) → k ≤ L → program.State × List (Fin n)
  | 0, _ => (program.start, [])
  | k + 1, hk =>
      let previous := executePrefix program input k (by omega)
      let layer : Fin L := ⟨k, by omega⟩
      let query := program.query? layer previous.1
      let answer := query.map input
      (program.next layer previous.1 answer, previous.2 ++ query.toList)

/-- State after all layers. -/
def finalState {n L : Nat} (program : LayeredQueryProgram n L)
    (input : Fin n → Bool) : program.State :=
  (executePrefix program input L le_rfl).1

/-- Output bit after all layers. -/
def eval {n L : Nat} (program : LayeredQueryProgram n L)
    (input : Fin n → Bool) : Bool :=
  program.output (program.finalState input)

/-- Chronological input-query trace. -/
def queryTrace {n L : Nat} (program : LayeredQueryProgram n L)
    (input : Fin n → Bool) : List (Fin n) :=
  (executePrefix program input L le_rfl).2

/-- A second input agrees with a reference execution on every coordinate
actually queried by that execution.  Coordinates outside the reference trace
are deliberately unconstrained. -/
def InputsAgreeOnQueryTrace {n L : Nat}
    (program : LayeredQueryProgram n L)
    (reference candidate : Fin n → Bool) : Prop :=
  ∀ coordinate ∈ program.queryTrace reference,
    candidate coordinate = reference coordinate

/-- Path-cylinder principle for a finite layered query program.  If a second
input supplies the same answers on the reference execution's query trace,
then every live state and query exposed by the two executions is identical.

The statement is directional only because the agreement premise names the
reference trace; the conclusion in particular proves that the candidate
trace is that same trace. -/
theorem executePrefix_eq_of_agree_on_reference_trace
    {n L : Nat} (program : LayeredQueryProgram n L)
    (reference candidate : Fin n → Bool)
    (k : Nat) (hk : k ≤ L)
    (hagree : ∀ coordinate ∈ (program.executePrefix reference k hk).2,
      candidate coordinate = reference coordinate) :
    program.executePrefix candidate k hk =
      program.executePrefix reference k hk := by
  induction k with
  | zero => simp [executePrefix]
  | succ k ih =>
      let referencePrefix := program.executePrefix reference k (by omega)
      let layer : Fin L := ⟨k, by omega⟩
      let query := program.query? layer referencePrefix.1
      have hagreePrefix : ∀ coordinate ∈ referencePrefix.2,
          candidate coordinate = reference coordinate := by
        intro coordinate hcoordinate
        apply hagree coordinate
        simp only [executePrefix]
        exact List.mem_append_left query.toList hcoordinate
      have hprefix : program.executePrefix candidate k (by omega) =
          referencePrefix := by
        exact ih (by omega) hagreePrefix
      simp only [executePrefix]
      rw [hprefix]
      have hanswer : query.map candidate = query.map reference := by
        cases hquery : query with
        | none => rfl
        | some coordinate =>
            simp only [Option.map_some]
            congr 1
            apply hagree coordinate
            simp only [executePrefix, List.mem_append]
            right
            simpa [query, layer, referencePrefix] using hquery
      simp [referencePrefix, layer, query, hanswer]

/-- Full-execution form of the path-cylinder principle. -/
theorem finalState_eq_of_inputsAgreeOnQueryTrace
    {n L : Nat} (program : LayeredQueryProgram n L)
    (reference candidate : Fin n → Bool)
    (hagree : program.InputsAgreeOnQueryTrace reference candidate) :
    program.finalState candidate = program.finalState reference := by
  exact congrArg Prod.fst
    (executePrefix_eq_of_agree_on_reference_trace
      program reference candidate L le_rfl hagree)

/-- Agreement on the reference trace preserves the Boolean output exactly. -/
theorem eval_eq_of_inputsAgreeOnQueryTrace
    {n L : Nat} (program : LayeredQueryProgram n L)
    (reference candidate : Fin n → Bool)
    (hagree : program.InputsAgreeOnQueryTrace reference candidate) :
    program.eval candidate = program.eval reference := by
  unfold eval
  rw [finalState_eq_of_inputsAgreeOnQueryTrace
    program reference candidate hagree]

/-- Agreement on the reference trace also preserves the trace itself. -/
theorem queryTrace_eq_of_inputsAgreeOnQueryTrace
    {n L : Nat} (program : LayeredQueryProgram n L)
    (reference candidate : Fin n → Bool)
    (hagree : program.InputsAgreeOnQueryTrace reference candidate) :
    program.queryTrace candidate = program.queryTrace reference := by
  exact congrArg Prod.snd
    (executePrefix_eq_of_agree_on_reference_trace
      program reference candidate L le_rfl hagree)

/-- Exact finite width of the homogeneous live-state carrier. -/
def width {n L : Nat} (program : LayeredQueryProgram n L) : Nat :=
  @Fintype.card program.State program.stateFintype

/-- Width upper bound. -/
def HasWidthAtMost {n L : Nat} (program : LayeredQueryProgram n L)
    (W : Nat) : Prop :=
  program.width ≤ W

/-- Every execution queries each input coordinate at most once. -/
def IsReadOnce {n L : Nat} (program : LayeredQueryProgram n L) : Prop :=
  ∀ input, (program.queryTrace input).Nodup

/-- The queried coordinate at each layer is hardwired and independent of the
live state. -/
def HasFixedQueryOrder {n L : Nat} (program : LayeredQueryProgram n L)
    (order : Fin L → Option (Fin n)) : Prop :=
  ∀ layer state, program.query? layer state = order layer

/-- Obliviousness: some fixed optional query is assigned to every layer. -/
def IsOblivious {n L : Nat} (program : LayeredQueryProgram n L) : Prop :=
  ∃ order, program.HasFixedQueryOrder order

/-- At most one coordinate is appended by each executed layer. -/
theorem executePrefix_trace_length_le {n L : Nat}
    (program : LayeredQueryProgram n L) (input : Fin n → Bool)
    (k : Nat) (hk : k ≤ L) :
    (program.executePrefix input k hk).2.length ≤ k := by
  induction k with
  | zero =>
      simp [executePrefix]
  | succ k ih =>
      let previous := program.executePrefix input k (by omega)
      let layer : Fin L := ⟨k, by omega⟩
      let query := program.query? layer previous.1
      have hprev : previous.2.length ≤ k := ih (by omega)
      have hquery : query.toList.length ≤ 1 := by
        cases query <;> simp
      change (previous.2 ++ query.toList).length ≤ k + 1
      simp only [List.length_append]
      omega

/-- A full trace contains at most one query per layer. -/
theorem queryTrace_length_le {n L : Nat}
    (program : LayeredQueryProgram n L) (input : Fin n → Bool) :
    (program.queryTrace input).length ≤ L := by
  exact executePrefix_trace_length_le program input L le_rfl

/-- The nonempty queries among the first `k` entries of a fixed optional
layer order. -/
def fixedQueryOrderPrefix {n L : Nat}
    (order : Fin L → Option (Fin n)) (k : Nat) (hk : k ≤ L) :
    List (Fin n) :=
  (List.ofFn fun i : Fin k => order (Fin.castLE hk i)).filterMap id

/-- Under a fixed query order, execution records exactly its nonempty prefix;
the input values and live-state trajectory cannot change the trace. -/
theorem executePrefix_trace_eq_fixedQueryOrderPrefix {n L : Nat}
    (program : LayeredQueryProgram n L) (input : Fin n → Bool)
    (order : Fin L → Option (Fin n))
    (hfixed : program.HasFixedQueryOrder order)
    (k : Nat) (hk : k ≤ L) :
    (program.executePrefix input k hk).2 =
      fixedQueryOrderPrefix order k hk := by
  induction k with
  | zero =>
      simp [executePrefix, fixedQueryOrderPrefix]
  | succ k ih =>
      simp only [executePrefix]
      rw [hfixed]
      rw [ih (by omega)]
      unfold fixedQueryOrderPrefix
      rw [List.ofFn_succ_last, List.filterMap_append]
      have hprefix :
          (fun i : Fin k => order (Fin.castLE (by omega) i)) =
            (fun i : Fin k => order (Fin.castLE hk i.castSucc)) := by
        funext i
        congr 1
      rw [hprefix]
      have hlast : (⟨k, by omega⟩ : Fin L) =
          Fin.castLE hk (Fin.last k) := Fin.ext rfl
      rw [hlast]
      cases order (Fin.castLE hk (Fin.last k)) <;> rfl

/-- If a fixed layer order has no duplicate nonempty entries, every execution
is read-once. -/
theorem isReadOnce_of_fixedQueryOrder_nodup {n L : Nat}
    (program : LayeredQueryProgram n L) (order : Fin L → Option (Fin n))
    (hfixed : program.HasFixedQueryOrder order)
    (hnodup : ((List.ofFn order).filterMap id).Nodup) :
    program.IsReadOnce := by
  intro input
  rw [queryTrace,
    executePrefix_trace_eq_fixedQueryOrderPrefix
      program input order hfixed L le_rfl]
  simpa [fixedQueryOrderPrefix] using hnodup

/-- Constant-zero program used for statically malformed fixed advice. -/
def constantReject (n L : Nat) : LayeredQueryProgram n L where
  State := Unit
  stateFintype := inferInstance
  start := ()
  query? := fun _ _ => none
  next := fun _ _ _ => ()
  output := fun _ => false

@[simp]
theorem constantReject_executePrefix (n L : Nat) (input : Fin n → Bool)
    (k : Nat) (hk : k ≤ L) :
    (constantReject n L).executePrefix input k hk = ((), []) := by
  induction k with
  | zero => simp [executePrefix, constantReject]
  | succ k ih =>
      simp only [executePrefix]
      rw [ih (by omega)]
      rfl

@[simp]
theorem constantReject_eval (n L : Nat) (input : Fin n → Bool) :
    (constantReject n L).eval input = false := by
  simp [eval, finalState, constantReject]

theorem constantReject_isReadOnce (n L : Nat) :
    (constantReject n L).IsReadOnce := by
  intro input
  simp [queryTrace]

theorem constantReject_isOblivious (n L : Nat) :
    (constantReject n L).IsOblivious := by
  exact ⟨fun _ => none, by simp [HasFixedQueryOrder, constantReject]⟩

@[simp]
theorem constantReject_width (n L : Nat) :
    (constantReject n L).width = 1 := by
  simp [width, constantReject]

end LayeredQueryProgram
end OneTapeMagnification
end Frontier
end Pnp4
