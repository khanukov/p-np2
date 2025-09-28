import Pnp2.Boolcube
import Utils.Nat

/-!
`Pnp2.Circuit.StraightLine` introduces a DAG-style representation of Boolean
circuits.  Unlike the tree-based datatype `Boolcube.Circuit` used elsewhere in
this repository, the straight-line representation keeps an explicit list of
primitive gates where each gate may feed into later ones multiple times.  This
matches the classical notion of *straight-line programs* and provides a natural
setting for reasoning about circuit size in the presence of sharing.

The current module focuses on the semantic side: we define the syntax, provide
an evaluation function, and expose the elementary notion of size (simply the
number of gates).  Later developments will relate this representation to the
existing tree-based circuits and use it to organise the gate-count recurrence
appearing in the `P ⊆ P/poly` formalisation.
-/

open Boolcube

namespace Boolcube

/--
Primitive operations allowed in our straight-line circuits.  The parameter
`m` records how many wires (inputs plus previously defined gates) are available
when constructing the operation.
-/
inductive StraightOp : ℕ → Type where
  | const {m : ℕ} (b : Bool) : StraightOp m
  | not   {m : ℕ} (i : Fin m) : StraightOp m
  | and   {m : ℕ} (i j : Fin m) : StraightOp m
  | or    {m : ℕ} (i j : Fin m) : StraightOp m
  deriving DecidableEq

namespace StraightOp

/--
Evaluate a primitive straight-line operation given access to all previous wire
values.  The helper is parameterised by a function returning the Boolean value
of each available wire.
-/
@[simp] def eval {m : ℕ} (op : StraightOp m) (wire : Fin m → Bool) : Bool :=
  match op with
  | const b => b
  | not i   => !(wire i)
  | and i j => wire i && wire j
  | or i j  => wire i || wire j

end StraightOp

/--
Straight-line circuits with `n` input bits.  The field `gate` assigns to each
position `g < gates` a primitive operation whose inputs range over the `n`
original variables together with the outputs of the previously defined `g`
gates.  The final output is selected by `output`, which may reference either an
input or an intermediate gate.
-/
structure StraightLineCircuit (n : ℕ) where
  gates  : ℕ
  gate   : (g : Fin gates) → StraightOp (n + g)
  output : Fin (n + gates)

namespace StraightLineCircuit

variable {n : ℕ}

/--
The straight-line size of a circuit is simply the number of explicit gates.
This quantity will later serve as the combinatorial measure feeding the
polynomial bounds for the Turing-machine simulation.
-/
@[simp] def size (C : StraightLineCircuit n) : ℕ := C.gates

/--
Internal helper used by `eval`.  The value `evalWireAux C x g hg i` computes the
Boolean carried by wire `i` assuming that only the first `g` gates of `C` are
available.  The proof `hg` witnesses that those gates lie within the circuit.
-/
mutual
  def evalWireAux (C : StraightLineCircuit n) (x : Point n) :
      ∀ {g : ℕ}, g ≤ C.gates → Fin (n + g) → Bool
    | g, hg, i =>
        let idx : ℕ := i
        have hlt : idx < n + g := by
          simpa [idx] using i.is_lt
        if h : idx < n then
          -- We are referring to one of the original input wires.
          x ⟨idx, h⟩
        else
          -- The wire points to a previously defined gate.  We reduce the index
          -- by the number of inputs to obtain a gate identifier below `g`.
          let j : ℕ := idx - n
          have hInputs : n ≤ idx := Nat.not_lt.mp h
          have hj_lt : j < g :=
            Nat.sub_lt_of_le_of_lt (a := idx) (b := n) (c := g) hInputs hlt
          have hj_total : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          evalGateAux C x j hj_total
  def evalGateAux (C : StraightLineCircuit n) (x : Point n) :
      ∀ {g : ℕ}, g < C.gates → Bool
    | g, hg =>
        let op := C.gate ⟨g, hg⟩
        StraightOp.eval op (fun w =>
          evalWireAux C x (g := g) (hg := Nat.le_of_lt hg) w)
termination_by
    evalWireAux g _ => g
    evalGateAux g _ => g
end

/--
Evaluate a straight-line circuit on an input assignment.  The definition simply
looks up the value of the wire designated by `output` once all gates have been
unfolded.
-/
noncomputable def eval (C : StraightLineCircuit n) (x : Point n) : Bool :=
  evalWireAux (C := C) (x := x) (g := C.gates) (hg := le_rfl) C.output

/--
Evaluate all wires of a straight-line circuit simultaneously.  This convenience
wrapper keeps the number of available gates fixed to the whole circuit, which
matches the typical use case when reasoning about sharing between subsequent
extensions.
-/
def evalWire (C : StraightLineCircuit n) (x : Point n) :
    Fin (n + C.gates) → Bool :=
  evalWireAux (C := C) (x := x) (g := C.gates) (hg := le_rfl)

@[simp] lemma eval_eq_evalWire (C : StraightLineCircuit n) (x : Point n) :
    eval C x = evalWire (C := C) (x := x) C.output := rfl

/--
Translate the straight-line representation of a wire into the inductive
Boolean-circuit datatype.  The auxiliary recursion mirrors `evalWireAux` and
rebuilds the referenced gates as tree circuits, thereby enabling us to reuse
the standard `Boolcube.Circuit` tooling when relating the straight-line and
tree-based models of computation.-/
mutual
  def toCircuitWireAux (C : StraightLineCircuit n) :
      ∀ {g : ℕ}, g ≤ C.gates → Fin (n + g) → Circuit n
    | g, hg, i =>
        if h : (i : ℕ) < n then
          Circuit.var ⟨i, h⟩
        else
          let j : ℕ := (i : ℕ) - n
          have hInputs : n ≤ (i : ℕ) := Nat.le_of_not_lt h
          have hj_lt : j < g :=
            Nat.sub_lt_of_le_of_lt hInputs (by simpa using i.is_lt)
          have hj_total : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          toCircuitGateAux (C := C) (g := j) hj_total

  /-- Auxiliary component of `toCircuitWireAux` reconstructing a single gate. -/
  def toCircuitGateAux (C : StraightLineCircuit n) :
      ∀ {g : ℕ}, g < C.gates → Circuit n
    | g, hg =>
        match C.gate ⟨g, hg⟩ with
        | StraightOp.const b => Circuit.const b
        | StraightOp.not i =>
            Circuit.not
              (toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) i)
        | StraightOp.and i j =>
            Circuit.and
              (toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) i)
              (toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) j)
        | StraightOp.or i j =>
            Circuit.or
              (toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) i)
              (toCircuitWireAux (C := C) (g := g) (hg := Nat.le_of_lt hg) j)
  termination_by
    toCircuitWireAux g _ _ => g
    toCircuitGateAux g _ => g
end

/-- Interpret a wire of a straight-line circuit as an ordinary Boolean circuit. -/
def toCircuitWire (C : StraightLineCircuit n) :
    Fin (n + C.gates) → Circuit n :=
  fun i => toCircuitWireAux (C := C) (g := C.gates) (hg := le_rfl) i

/-- Translate the designated output wire of a straight-line circuit. -/
def toCircuit (C : StraightLineCircuit n) : Circuit n :=
  toCircuitWire (C := C) C.output

/--
Evaluation of the translated objects agrees with the straight-line semantics.
-/
mutual
  theorem eval_toCircuitWireAux (C : StraightLineCircuit n) :
      ∀ {g : ℕ} {hg : g ≤ C.gates} {i : Fin (n + g)} {x : Point n},
        Circuit.eval (toCircuitWireAux (C := C) (g := g) (hg := hg) i) x =
          StraightLineCircuit.evalWireAux (C := C) (x := x) (g := g) (hg := hg) i
    | g, hg, i, x => by
        classical
        by_cases h : (i : ℕ) < n
        · have hi : (⟨(i : ℕ), h⟩ : Fin n) = ⟨i, h⟩ := rfl
          simpa [toCircuitWireAux, h, StraightLineCircuit.evalWireAux, hi]
        · set j : ℕ := (i : ℕ) - n with hj
          have hInputs : n ≤ (i : ℕ) := Nat.le_of_not_lt h
          have hj_lt : j < g := by
            have := i.is_lt
            have := Nat.sub_lt_of_le_of_lt hInputs (by simpa [hj] using this)
            simpa [hj] using this
          have hj_total : j < C.gates := Nat.lt_of_lt_of_le hj_lt hg
          have hGate := eval_toCircuitGateAux (C := C) (g := j) (hg := hj_total)
              (x := x)
          simp [toCircuitWireAux, h, hj, StraightLineCircuit.evalWireAux,
            hInputs, hj_lt, hGate]

  theorem eval_toCircuitGateAux (C : StraightLineCircuit n) :
      ∀ {g : ℕ} {hg : g < C.gates} {x : Point n},
        Circuit.eval (toCircuitGateAux (C := C) (g := g) hg) x =
          StraightLineCircuit.evalGateAux (C := C) (x := x) (g := g) hg
    | g, hg, x => by
        classical
        cases hOp : C.gate ⟨g, hg⟩ with
        | const b =>
            simp [toCircuitGateAux, hOp, StraightLineCircuit.evalGateAux]
        | not i =>
            simp [toCircuitGateAux, hOp, StraightLineCircuit.evalGateAux,
              StraightOp.eval, eval_toCircuitWireAux]
        | and i j =>
            simp [toCircuitGateAux, hOp, StraightLineCircuit.evalGateAux,
              StraightOp.eval, eval_toCircuitWireAux]
        | or i j =>
            simp [toCircuitGateAux, hOp, StraightLineCircuit.evalGateAux,
              StraightOp.eval, eval_toCircuitWireAux]
end

@[simp] lemma eval_toCircuitWire (C : StraightLineCircuit n) (x : Point n)
    (i : Fin (n + C.gates)) :
    Circuit.eval (toCircuitWire (C := C) i) x =
      StraightLineCircuit.evalWire (C := C) (x := x) i := by
  simpa [toCircuitWire, StraightLineCircuit.evalWire]
    using eval_toCircuitWireAux (C := C) (hg := le_rfl) (i := i) (x := x)

@[simp] lemma eval_toCircuit (C : StraightLineCircuit n) (x : Point n) :
    Circuit.eval (toCircuit (C := C)) x = StraightLineCircuit.eval C x := by
  simpa [toCircuit, StraightLineCircuit.eval_eq_evalWire, toCircuitWire]
    using eval_toCircuitWire (C := C) (x := x) C.output

/--
Evaluation of an input wire ignores the gate structure and simply projects
the corresponding bit of the assignment `x`.  The lemma is phrased in terms of
the canonical embedding of `Fin n` into the extended index set `Fin (n +
gates)` used by the straight-line representation.
-/
@[simp] lemma evalWire_input (C : StraightLineCircuit n) (x : Point n)
    (i : Fin n) :
    evalWire (C := C) (x := x)
        ⟨i, by
          -- Every input index is automatically below `n + C.gates` because
          -- the latter extends the former by a non-negative amount.
          have : (i : ℕ) < n := i.is_lt
          exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)⟩ =
      x i := by
  -- We expand the definition of `evalWire` to expose the recursive helper.
  unfold evalWire
  -- The wire index projects back to `i` and therefore falls in the input
  -- range.  The corresponding branch of `evalWireAux` simply returns `x i`.
  simp [StraightLineCircuit.evalWireAux, dif_pos]

/--
Embed an existing wire into a circuit extended by a single additional gate.
Conceptually this is the identity map on wire indices, viewed inside the
larger ambient space.
-/
def liftWire (C : StraightLineCircuit n) :
    Fin (n + C.gates) → Fin (n + (C.gates + 1)) :=
  fun i =>
    ⟨i, by
      have h₁ : (i : ℕ) < n + C.gates := i.is_lt
      have h₂ : n + C.gates < n + (C.gates + 1) := by
        have := Nat.lt_succ_self (n + C.gates)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using this
      exact Nat.lt_trans h₁ h₂⟩

/--
Changing the designated output wire leaves the underlying circuit untouched;
only the final lookup is redirected.
-/
def withOutput (C : StraightLineCircuit n)
    (out : Fin (n + C.gates)) : StraightLineCircuit n :=
  { C with output := out }

@[simp] lemma eval_withOutput (C : StraightLineCircuit n)
    (out : Fin (n + C.gates)) (x : Point n) :
    eval (withOutput (C := C) out) x = evalWire (C := C) (x := x) out := rfl

/--
Append a new gate to the end of a straight-line circuit.  The freshly inserted
gate becomes the default output, while all existing gates remain available for
reuse in subsequent constructions.
-/
def snoc (C : StraightLineCircuit n) (op : StraightOp (n + C.gates)) :
    StraightLineCircuit n :=
  { gates := C.gates + 1
    , gate := fun g =>
        if h : (g : ℕ) < C.gates then
          by
            -- In this branch we reuse one of the existing gates verbatim.
            simpa using (C.gate ⟨g, h⟩)
        else
          by
            -- The last index corresponds to the newly appended gate, whose
            -- inputs are described by `op`.
            have hle : (g : ℕ) ≤ C.gates :=
              Nat.lt_succ_iff.mp (by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                  using g.is_lt)
            have hge : C.gates ≤ (g : ℕ) := Nat.le_of_not_lt h
            have hg : (g : ℕ) = C.gates := Nat.le_antisymm hle hge
            simpa [hg] using (show StraightOp (n + C.gates) from op)
    , output := Fin.last (n + (C.gates + 1)) }

@[simp] lemma size_snoc (C : StraightLineCircuit n)
    (op : StraightOp (n + C.gates)) :
    (snoc (C := C) op).size = C.size + 1 := by
  simp [snoc, StraightLineCircuit.size, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]


/--
Evaluation of existing wires is unaffected by appending a new gate.  The proof
proceeds by a simultaneous induction on the number of available gates,
following the recursive structure of `evalWireAux` and `evalGateAux`.
-/
mutual
  lemma evalWireAux_snoc_old (C : StraightLineCircuit n)
      (op : StraightOp (n + C.gates)) (x : Point n) :
      ∀ {g : ℕ} (hg : g ≤ C.gates) (i : Fin (n + g)),
        evalWireAux (C := snoc (C := C) op) (x := x)
            (g := g) (hg := Nat.le_trans hg (Nat.le_succ _)) i =
          evalWireAux (C := C) (x := x) (g := g) (hg := hg) i
    | 0, _, i =>
        -- Base case: only the input wires are visible.
        by
          simp [evalWireAux]
    | Nat.succ g, hg, i => by
        -- Inductive step: either we access an input wire or recurse on a gate.
        have hlt : (i : ℕ) < n + (Nat.succ g) := i.is_lt
        by_cases hInput : (i : ℕ) < n
        · simp [evalWireAux, hInput]
        · -- Translate the index to the corresponding gate position.
          have hInputs : n ≤ (i : ℕ) := Nat.le_of_not_lt hInput
          set j : ℕ := (i : ℕ) - n
          have hj_lt : j < Nat.succ g := by
            simpa [j]
              using Nat.sub_lt_of_le_of_lt (a := (i : ℕ)) (b := n)
                (c := Nat.succ g) hInputs hlt
          have hj_gate : j < C.gates :=
            Nat.lt_of_lt_of_le hj_lt hg
          have hj_snoc : j < (snoc (C := C) op).gates := by
            have : j < C.gates + 1 :=
              Nat.lt_of_lt_of_le hj_gate (Nat.le_succ _)
            simpa [snoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
          -- Reuse the inductive hypotheses for the gate computation.
          have ihGate := evalGateAux_snoc_old (n := n) (C := C)
            (op := op) (x := x) (g := j) hj_gate
          -- With the gate equality in hand the wire equality follows.
          simp [evalWireAux, hInput, j, hj_lt, hInputs, snoc, ihGate]
  lemma evalGateAux_snoc_old (C : StraightLineCircuit n)
      (op : StraightOp (n + C.gates)) (x : Point n) :
      ∀ {g : ℕ} (hg : g < C.gates),
        evalGateAux (C := snoc (C := C) op) (x := x)
            (g := g) (hg := Nat.lt_of_lt_of_le hg (Nat.le_succ _)) =
          evalGateAux (C := C) (x := x) (g := g) (hg := hg)
    | g, hg => by
        -- The appended circuit reuses the old operation for indices `g < gates`.
        have hgate :
            (snoc (C := C) op).gate ⟨g, Nat.lt_of_lt_of_le hg (Nat.le_succ _)⟩ =
              C.gate ⟨g, hg⟩ := by
          simp [snoc, hg]
        -- Apply the inductive hypothesis to the wire lookup.
        have hwire := evalWireAux_snoc_old (n := n) (C := C) (op := op)
          (x := x) (g := g) (hg := Nat.le_of_lt hg)
        simp [evalGateAux, hgate, hwire]
end

/-- Evaluation of an existing wire is preserved when appending a gate. -/
@[simp] lemma evalWire_snoc_lift (C : StraightLineCircuit n)
    (op : StraightOp (n + C.gates)) (x : Point n)
    (i : Fin (n + C.gates)) :
    evalWire (C := snoc (C := C) op) (x := x)
        (liftWire (C := C) i) =
      evalWire (C := C) (x := x) i := by
  simpa [evalWire, liftWire]
    using evalWireAux_snoc_old (n := n) (C := C) (op := op) (x := x)
      (g := C.gates) (hg := le_rfl) i

/--
The newly appended gate computes exactly the primitive operation supplied to
`snoc` when evaluated on the existing wires of the circuit.
-/
lemma eval_snoc (C : StraightLineCircuit n)
    (op : StraightOp (n + C.gates)) (x : Point n) :
    eval (snoc (C := C) op) x =
      StraightOp.eval op (fun w => evalWire (C := C) (x := x) w) := by
  -- The output of `snoc` is the last gate, which corresponds to `op`.
  have hgate :
      (snoc (C := C) op).gate
          ⟨C.gates, by
            have := Nat.lt_succ_self C.gates
            simpa [snoc] using this⟩ =
        cast (by simp [snoc]) op := by
    -- Direct simplification reveals the appended operation.
    simp [snoc]
  -- Evaluate the appended gate using the previously established wire equality.
  simp [eval, evalGateAux, hgate, evalWire_snoc_lift, evalWire]

end StraightLineCircuit

end Boolcube


/--
The subsequent development manipulates straight-line circuits by appending a
controlled number of gates while keeping track of the indices of previously
defined wires.  The auxiliary structures introduced below provide a light-weight
"builder" abstraction that records the current circuit together with a proof
that every original wire remains in range.  Each freshly added gate yields a
`Wire` token remembering its numeric index and an upper bound witnessing that
the index stays valid once further gates are appended.  The bookkeeping will be
used in the `P ⊆ P/poly` proof to construct straight-line layers whose size can
be estimated directly from the number of appended gates.
-/
namespace Boolcube
namespace StraightLineCircuit

/--
Token remembering the index of a wire in a straight-line circuit together with
an upper bound on the number of gates that were available when the token was
created.  The inequality `idx < n + bound` ensures that as long as the circuit
eventually grows to have at least `bound` gates, the token may be safely
interpreted as an index into the extended circuit.
-/
structure Wire (n : ℕ) where
  idx   : ℕ
  bound : ℕ
  bound_lt : idx < n + bound

namespace Wire

variable {n : ℕ}

/--
Convert a concrete `Fin` index into a reusable wire token.  The token records
the ambient gate count `g` required for the index to be valid; as the circuit
grows, the token can be reinterpreted in any larger context without recomputing
the underlying arithmetic bounds.
-/
def ofFin {g : ℕ} (w : Fin (n + g)) : Wire n :=
  { idx := w
    , bound := g
    , bound_lt := by
        simpa using w.is_lt }

@[simp] lemma ofFin_idx {g : ℕ} (w : Fin (n + g)) : (ofFin (n := n) (g := g) w).idx = w := rfl

@[simp] lemma ofFin_bound {g : ℕ} (w : Fin (n + g)) : (ofFin (n := n) (g := g) w).bound = g := rfl

/-- Restoring a token produced by `ofFin` in a circuit with exactly `g` gates
recovers the original index. -/
@[simp] lemma toFin_ofFin {g : ℕ} (w : Fin (n + g)) :
    (ofFin (n := n) (g := g) w).toFin (n := n) (g := g) (Nat.le_of_eq rfl) = w := by
  ext <;> rfl

/--
Cast a wire token into an actual `Fin` index once the surrounding circuit is
known to contain at least `bound` gates.  The resulting index targets
`Fin (n + g)`, matching the wire namespace of a circuit with `g` gates.
-/
def toFin (w : Wire n) {g : ℕ} (hg : w.bound ≤ g) : Fin (n + g) :=
  ⟨w.idx, by
    have := w.bound_lt
    have hle := Nat.add_le_add_left hg n
    exact Nat.lt_of_lt_of_le this hle⟩

@[simp] lemma toFin_idx {w : Wire n} {g : ℕ} (hg : w.bound ≤ g) :
    ((w.toFin (n := n) (g := g) hg : Fin (n + g)) : ℕ) = w.idx := rfl

end Wire

/--
Mutable view on a straight-line circuit `base`.  The builder stores an extended
 circuit together with a proof that every original wire of `base` remains within
bounds.  Subsequent gate insertions only update the `circuit` field while the
monotonicity proof `base_le` evolves by transitivity.
-/
structure Builder (n : ℕ) (base : StraightLineCircuit n) where
  circuit : StraightLineCircuit n
  base_le : base.gates ≤ circuit.gates

namespace Builder

variable {n : ℕ} {base : StraightLineCircuit n}

/--
Fold a list of wires using Boolean disjunction, evaluating each wire inside the
same circuit.  The accumulator initialises to `false`, matching the identity
element for OR.
-/
def evalList (C : StraightLineCircuit n) (x : Point n)
    (ws : List (Fin (n + C.gates))) : Bool :=
  ws.foldl (fun acc w => acc || StraightLineCircuit.evalWire (C := C) (x := x) w)
    false

/--
Evaluating a concatenated list of wires splits as the disjunction of the two
parts.  The result is immediate from the `foldl` characterisation of
`StraightLineCircuit.evalList` together with the associativity and commutativity
of Boolean `or`.-/
lemma evalList_append (C : StraightLineCircuit n) (x : Point n)
    (ws₁ ws₂ : List (Fin (n + C.gates))) :
    evalList (C := C) (x := x) (ws₁ ++ ws₂) =
      (evalList (C := C) (x := x) ws₁) ||
        (evalList (C := C) (x := x) ws₂) := by
  induction ws₁ generalizing ws₂ with
  | nil =>
      simp [evalList]
  | cons w ws ih =>
      intro ws₂
      -- Expand the definition and apply the standard `foldl` append law to
      -- expose the inductive hypothesis.
      simp [evalList, List.foldl_append, ih, Bool.or_assoc, Bool.or_left_comm,
        Bool.or_comm]

/-- Start the builder with the original circuit. -/
@[simp] def mk (base : StraightLineCircuit n) : Builder n base :=
  { circuit := base, base_le := le_rfl }

/--
Lift an input or previously created wire of the base circuit into the ambient
builder circuit.  The proof `base_le` guarantees that the index stays within
range after any number of gate insertions.
-/
def liftBase (b : Builder n base) (i : Fin (n + base.gates)) :
    Fin (n + b.circuit.gates) :=
  ⟨i, by
    have := i.is_lt
    have hle := Nat.add_le_add_left b.base_le n
    exact Nat.lt_of_lt_of_le this hle⟩

/--
Token corresponding to a base wire.  The bound is instantiated with the number
of gates of the original circuit, meaning that the token may be interpreted in
any extension produced by the builder.
-/
def baseWire (b : Builder n base) (i : Fin (n + base.gates)) : Wire n :=
  { idx := i
    , bound := base.gates
    , bound_lt := by
        simpa using i.is_lt }

/--
Append a new gate to the current circuit, returning both the updated builder and
the wire token pointing to the freshly created gate.  The token records the
total number of gates of the new circuit as its bound, which is the minimal
context in which the wire is available.
-/
def append (b : Builder n base) (op : StraightOp (n + b.circuit.gates)) :
    Builder n base × Wire n :=
  let circuit' := StraightLineCircuit.snoc b.circuit op
  let builder' : Builder n base :=
    { circuit := circuit'
      , base_le :=
          Nat.le_trans b.base_le (Nat.le_of_lt (Nat.lt_succ_self _)) }
  let idx := n + b.circuit.gates
  let bound := circuit'.gates
  have hlt : idx < n + bound := by
    have : (n + b.circuit.gates) < n + (b.circuit.gates + 1) :=
      Nat.lt_succ_self _
    simpa [idx, bound, circuit', StraightLineCircuit.snoc, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
      using this
  let wire : Wire n :=
    { idx := idx, bound := bound, bound_lt := hlt }
  (builder', wire)

@[simp] lemma append_circuit (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    (b.append op).fst.circuit = StraightLineCircuit.snoc b.circuit op := rfl

@[simp] lemma append_bound (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    (b.append op).snd.bound = (StraightLineCircuit.snoc b.circuit op).gates := rfl

/--
Interpret the wire token returned by `append` as the last gate of the updated
 circuit.  The coercion reduces to `Fin.last`, which greatly simplifies
evaluation lemmas.
-/
lemma append_wire_toFin (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    let result := b.append op
    result.snd.toFin (n := n) (g := result.fst.circuit.gates) (by
      simpa [append_circuit] using le_rfl) =
      Fin.last (n + (b.circuit.gates + 1)) := by
  -- Expand the definitions to expose the numeric components of the token.
  unfold append
  simp [Wire.toFin, StraightLineCircuit.snoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

/--
Evaluation of the freshly appended gate: the resulting wire computes exactly the
primitive operation supplied to `append`.  This is a restatement of
`StraightLineCircuit.eval_snoc` in terms of the builder interface.
-/
lemma append_eval (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) (x : Point n) :
    let result := b.append op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (result.snd.toFin (n := n)
          (g := result.fst.circuit.gates)
          (by
            have := le_rfl
            simpa [append_circuit] using this)) =
      StraightOp.eval op (fun w =>
        StraightLineCircuit.evalWire (C := b.circuit) (x := x) w) := by
  -- The appended gate is the last entry of the new circuit.  Evaluating it is
  -- precisely `StraightLineCircuit.eval_snoc`.
  unfold append
  simp [StraightLineCircuit.eval_snoc, StraightLineCircuit.snoc,
    StraightLineCircuit.eval_eq_evalWire]

/--
Convenience wrapper returning the freshly appended gate directly as a `Fin`
index into the updated circuit.  The bound inequality required by `Wire.toFin`
is immediate because the token records the exact number of gates after the
insertion.
-/
def appendFin (b : Builder n base) (op : StraightOp (n + b.circuit.gates)) :
    Builder n base × Fin (n + (StraightLineCircuit.snoc b.circuit op).gates) :=
  let result := b.append op
  have hbound : result.snd.bound ≤ result.fst.circuit.gates := by
    -- Rewriting with `append_circuit` and `append_bound` shows both sides agree.
    simpa [append_bound, append_circuit] using (le_of_eq (rfl))
  ( result.fst
  , result.snd.toFin (n := n) (g := result.fst.circuit.gates) hbound )

@[simp] lemma appendFin_fst (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    (b.appendFin op).fst.circuit = StraightLineCircuit.snoc b.circuit op := by
  unfold appendFin
  simp [append_circuit]

@[simp] lemma appendFin_snd_coe (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    ((b.appendFin op).snd : ℕ) = n + b.circuit.gates := by
  unfold appendFin
  simp [Wire.toFin, append_circuit, StraightLineCircuit.snoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The number of gates after appending equals the previous count plus one. -/
@[simp] lemma appendFin_gate_eq (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    (b.appendFin op).fst.circuit.gates = b.circuit.gates + 1 := by
  simp [appendFin_fst, StraightLineCircuit.snoc]

/--
Evaluation rule for the `appendFin` convenience wrapper.  The statement is a
direct corollary of `append_eval`.
-/
lemma appendFin_eval (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) (x : Point n) :
    let result := b.appendFin op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
      StraightOp.eval op (fun w =>
        StraightLineCircuit.evalWire (C := b.circuit) (x := x) w) := by
  unfold appendFin
  simp [append_eval]

/--
After appending a gate we may reinterpret existing wires inside the extended
circuit via `liftWire`.  This helper packages the coercion so that the codomain
is phrased in terms of the updated builder.
-/
def appendFin_lift (b : Builder n base) (op : StraightOp (n + b.circuit.gates)) :
    let result := b.appendFin op
    Fin (n + b.circuit.gates) → Fin (n + result.fst.circuit.gates) :=
  fun w => by
    have hg : (b.appendFin op).fst.circuit.gates = b.circuit.gates + 1 :=
      appendFin_gate_eq (b := b) (op := op)
    -- Transport the index using `liftWire` followed by the numerical identity.
    simpa [appendFin_fst, StraightLineCircuit.snoc, hg,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (StraightLineCircuit.liftWire (C := b.circuit) w)

/--
Shorthand constructors for appending primitive Boolean gates.  These helpers are
purely notational but greatly improve readability when constructing elaborate
layers.
-/
def appendConst (b : Builder n base) (val : Bool) : Builder n base × Wire n :=
  b.append (StraightOp.const val)

def appendNot (b : Builder n base)
    (w : Fin (n + b.circuit.gates)) : Builder n base × Wire n :=
  b.append (StraightOp.not w)

def appendAnd (b : Builder n base)
    (u v : Fin (n + b.circuit.gates)) : Builder n base × Wire n :=
  b.append (StraightOp.and u v)

def appendOr (b : Builder n base)
    (u v : Fin (n + b.circuit.gates)) : Builder n base × Wire n :=
  b.append (StraightOp.or u v)

/--
Variant of `appendConst` returning the resulting wire as a `Fin` index.  The
type of the ambient circuit is expressed via `snoc` to reflect the newly
inserted gate.
-/
def appendConstFin (b : Builder n base) (val : Bool) :
    Builder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.const val)).gates) :=
  b.appendFin (StraightOp.const val)

/--
Variant of `appendNot` returning the freshly created wire as a `Fin` index.
-/
def appendNotFin (b : Builder n base)
    (w : Fin (n + b.circuit.gates)) :
    Builder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.not w)).gates) :=
  b.appendFin (StraightOp.not w)

/--
Variant of `appendAnd` returning the resulting wire as a `Fin` index.
-/
def appendAndFin (b : Builder n base)
    (u v : Fin (n + b.circuit.gates)) :
    Builder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.and u v)).gates) :=
  b.appendFin (StraightOp.and u v)

/--
Variant of `appendOr` returning the resulting wire as a `Fin` index.
-/
def appendOrFin (b : Builder n base)
    (u v : Fin (n + b.circuit.gates)) :
    Builder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.or u v)).gates) :=
  b.appendFin (StraightOp.or u v)

/--
Accumulate a non-empty list of wires using OR gates.  When the list contains a
single element the builder stays untouched; otherwise we repeatedly append a new
gate computing the disjunction of the first two wires and continue with the
result prepended to the remaining list.  For the degenerate empty list we
produce an explicit `false` constant so that the function is total.
-/
def appendBigOr
    (b : Builder n base) :
    List (Fin (n + b.circuit.gates)) → Σ' (b' : Builder n base),
      Fin (n + b'.circuit.gates)
  | [] =>
      let result := appendConstFin (b := b) false
      ⟨result.fst, result.snd⟩
  | [w] => ⟨b, w⟩
  | w :: w' :: rest =>
      let result := appendOrFin (b := b) w w'
      let lift := appendFin_lift (b := b) (op := StraightOp.or w w')
      let rest' := rest.map lift
      appendBigOr (b := result.fst) (result.snd :: rest')
  termination_by
    appendBigOr b ws => ws.length

/--
The gate produced by `appendBigOr` evaluates to the Boolean disjunction of the
input wires when interpreted in the original circuit.
-/
lemma appendBigOr_eval (b : Builder n base)
    (ws : List (Fin (n + b.circuit.gates))) (x : Point n) :
    let result := appendBigOr (b := b) ws
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
      evalList (C := b.circuit) (x := x) ws := by
  classical
  induction ws with
  | nil =>
      simp [appendBigOr, evalList, appendConstFin, appendFin_eval]
  | cons w ws ih =>
      cases ws with
      | nil =>
          simp [appendBigOr, evalList]
      | cons w' ws' =>
          -- Expand the recursive definition and use the induction hypothesis.
          have := ih
          -- Simplify the lifted evaluations using `evalWire_snoc_lift`.
          simp [appendBigOr, evalList, appendFin_eval, Bool.or_assoc,
            Bool.or_left_comm, Bool.or_comm, appendFin_lift,
            StraightLineCircuit.evalWire_snoc_lift] at this
          simpa using this

/--
Specialised version of `appendBigOr` operating on evaluation-aware builders.
The implementation mirrors the raw builder recursion but stays within the
`EvalBuilder` interface so that the lifting invariants are preserved
automatically.
-/
def EvalBuilder.appendBigOr (b : EvalBuilder n base) :
    List (Fin (n + b.circuit.gates)) →
      Σ' (b' : EvalBuilder n base), Fin (n + b'.circuit.gates)
  | [] =>
      let result := b.appendConstFin false
      ⟨result.fst, result.snd⟩
  | [w] => ⟨b, w⟩
  | w :: w' :: rest =>
      let result := b.appendOrFin w w'
      let lift := b.appendFin_lift (op := StraightOp.or w w')
      let rest' := rest.map lift
      EvalBuilder.appendBigOr (b := result.fst) (result.snd :: rest')
  termination_by
    EvalBuilder.appendBigOr b ws => ws.length

/--
Evaluation rule for the `EvalBuilder` variant of `appendBigOr`.  The resulting
wire computes the disjunction of the supplied wires when interpreted in the
original circuit.
-/
lemma EvalBuilder.appendBigOr_eval (b : EvalBuilder n base)
    (ws : List (Fin (n + b.circuit.gates))) (x : Point n) :
    let result := EvalBuilder.appendBigOr (b := b) ws
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x) result.snd =
      evalList (C := b.circuit) (x := x) ws := by
  classical
  induction ws with
  | nil =>
      simp [EvalBuilder.appendBigOr, evalList, appendConstFin_eval]
  | cons w ws ih =>
      cases ws with
      | nil =>
          simp [EvalBuilder.appendBigOr, evalList]
      | cons w' ws' =>
          -- Unfold the recursion and recycle the induction hypothesis on the
          -- residual list.
          have := ih
          -- The inductive statement is phrased for the lifted wires.
          simp [EvalBuilder.appendBigOr, evalList, appendOrFin_eval,
            Bool.or_assoc, Bool.or_left_comm, Bool.or_comm,
            EvalBuilder.appendFin_lift, StraightLineCircuit.evalWire_snoc_lift]
            at this
          simpa using this

/-- Appending a `bigOr` does not modify the semantics of previously existing
wires.  The proof follows the recursive structure of
`EvalBuilder.appendBigOr`, applying the general preservation lemma for
`appendFin` at each step. -/
lemma EvalBuilder.appendBigOr_evalWire_preserved (b : EvalBuilder n base)
    (ws : List (Fin (n + b.circuit.gates)))
    (w : StraightLineCircuit.Wire n) (hw : w.bound ≤ b.circuit.gates)
    (x : Point n) :
    let result := EvalBuilder.appendBigOr (b := b) ws
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (w.toFin (n := n) (g := result.fst.circuit.gates)
          (by
            -- Every invocation of `appendBigOr` only increases the number of
            -- available gates.  Consequently any previously valid bound stays
            -- admissible for the extended builder.
            have hmono : b.circuit.gates ≤ result.fst.circuit.gates :=
              EvalBuilder.appendBigOr_gate_le (b := b) (ws := ws)
            exact Nat.le_trans hw hmono)) =
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
        (w.toFin (n := n) (g := b.circuit.gates) hw) := by
  classical
  revert b
  refine List.rec ?baseCase ?stepCase ws
  · intro b
    intro w hw x
    -- The empty list degenerates to appending a single `false` constant.
    simp [EvalBuilder.appendBigOr, EvalBuilder.appendConstFin,
      StraightLineCircuit.Wire.toFin_ofFin,
      appendFin_evalWire_preserved]  -- `appendFin` already preserves wires.
  · intro head tail ih b
    cases tail with
    | nil =>
        -- A singleton list leaves the builder untouched, whence the equality
        -- becomes reflexive.
        intro w hw x
        simp [EvalBuilder.appendBigOr]
    | cons head' tail' =>
        intro w hw x
        -- Expand the recursive call to expose the intermediate builder.
        dsimp [EvalBuilder.appendBigOr]
        -- The first step appends an OR gate between the leading two wires.
        set result := EvalBuilder.appendOrFin (b := b) head head' with hresult
        -- Subsequent recursive calls operate on the lifted tail.
        set lift := EvalBuilder.appendFin_lift
          (b := b) (op := StraightOp.or head head') with hlift
        set rest := tail'.map lift with hrest
        -- The recursion processes `result.snd :: rest` using the updated builder.
        have hmono : b.circuit.gates ≤ result.fst.circuit.gates := by
          -- Appending an OR gate increases the gate count by one.
          simpa [result, EvalBuilder.appendOrFin]
            using Nat.le_succ b.circuit.gates
        have hw' : w.bound ≤ result.fst.circuit.gates := Nat.le_trans hw hmono
        -- Invoke the induction hypothesis on the shortened list.
        have hIH := ih (b := result.fst) (w := w) (hw := hw') (x := x)
        -- Reinterpret the conclusion in terms of the original builder.
        have hPres :=
          appendFin_evalWire_preserved (b := b)
            (op := StraightOp.or head head') (w := w) (hw := hw) (x := x)
        -- Combine the two equalities.
        simpa [result, rest, EvalBuilder.appendBigOr, hlift]
          using hIH.trans hPres

/--
Appending a `bigOr` may introduce several auxiliary gates.  The following
estimate bounds the increase solely in terms of the length of the processed
wire list.  The coarse linear bound is sufficient for later size arguments
where we only need to know that each additional disjunct contributes a constant
number of gates.-/
lemma EvalBuilder.appendBigOr_gate_le_linear
    {base : StraightLineCircuit n}
    (b : EvalBuilder n base) (ws : List (Fin (n + b.circuit.gates))) :
    let result := EvalBuilder.appendBigOr (b := b) ws
    result.fst.circuit.gates ≤ b.circuit.gates + 2 * ws.length + 1 := by
  classical
  -- Prove the statement by induction on the length of the processed list.
  -- The auxiliary lemma `aux` keeps track of the length explicitly so that the
  -- recursive call can work with the shortened list arising in the `cons` case.
  have aux : ∀ k : ℕ,
      ∀ {b : EvalBuilder n base}
        {ws : List (Fin (n + b.circuit.gates))},
        ws.length = k →
          let result := EvalBuilder.appendBigOr (b := b) ws
          in result.fst.circuit.gates ≤
            b.circuit.gates + 2 * ws.length + 1 := by
    intro k
    induction k with
    | zero =>
        intro b ws hlen
        -- A zero-length list is necessarily empty, so `appendBigOr` reduces to
        -- appending a single constant gate.
        have hnil : ws = [] := List.length_eq_zero.mp hlen
        subst hnil
        simp [EvalBuilder.appendBigOr]
    | succ k ih =>
        intro b ws hlen
        -- Analyse the structure of the list with `length = k + 1`.
        cases ws with
        | nil =>
            cases hlen
        | cons w tail =>
            cases tail with
            | nil =>
                -- A singleton list keeps the builder unchanged.
                simp [EvalBuilder.appendBigOr, Nat.mul_succ, Nat.mul_zero,
                  Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc]
            | cons w' rest =>
                -- The general case: append one OR gate and recurse on the
                -- shortened list obtained after lifting indices.
                -- Convert the length assumption into information about the
                -- tail `rest`.
                have hlen' : Nat.succ (rest.length + 1) = Nat.succ k := by
                  simpa [List.length, Nat.succ_eq_add_one, Nat.add_comm,
                    Nat.add_left_comm, Nat.add_assoc]
                    using hlen
                have hrest : rest.length + 1 = k := Nat.succ.inj hlen'
                -- Unfold the recursive call.
                set result := EvalBuilder.appendOrFin (b := b) w w' with hresult
                set lift := EvalBuilder.appendFin_lift
                  (b := b) (op := StraightOp.or w w') with hlift
                set rest' := rest.map lift with hrest'
                -- The lifted list preserves the length of `rest`.
                have hlen_rest' : rest'.length = rest.length := by
                  simpa [rest', hlift]
                -- The recursive invocation of `appendBigOr` receives a list of
                -- length `k` (one shorter than the current list).
                have hlen_rec :
                    (result.snd :: rest').length = k := by
                  simp [rest', hlen_rest', hrest, Nat.succ_eq_add_one,
                    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                -- Apply the induction hypothesis to the shortened list.
                have hIH := ih (b := result.fst)
                  (ws := result.snd :: rest') hlen_rec
                -- The current step contributes a single additional gate.
                have hgate : result.fst.circuit.gates = b.circuit.gates + 1 := by
                  simpa [result, EvalBuilder.appendOrFin]
                    using EvalBuilder.appendFin_gate_eq
                      (b := b) (op := StraightOp.or w w')
                -- Combine the contributions and compare with the claimed bound.
                -- The recursive call processes a list of length `k`, whence the
                -- overall growth is at most `2 * k + 2` gates.
                have := hIH
                -- Simplify the recursive estimate using the length information.
                have hlen_ws : (w :: w' :: rest).length = Nat.succ k := by
                  simpa [List.length, Nat.succ_eq_add_one, Nat.add_comm,
                    Nat.add_left_comm, Nat.add_assoc] using hlen
                -- Rewrite everything in terms of the original builder.
                simpa [EvalBuilder.appendBigOr, result, rest', hgate,
                  Nat.mul_succ, Nat.mul_add, Nat.succ_eq_add_one,
                  Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hlen_ws]
                  using Nat.le_trans this (Nat.le_of_lt (Nat.lt_succ_self _))
  -- Instantiate the auxiliary lemma with the concrete length of `ws`.
  exact aux ws.length rfl

/--
Evaluation-aware builders remember that base wires keep their semantics after
additional gates are appended.  The invariant will let us reason about
straight-line encodings of configurations without repeatedly unfolding the
underlying circuit extensions.
-/
structure EvalBuilder (n : ℕ) (base : StraightLineCircuit n) where
  builder : Builder n base
  eval_liftBase :
    ∀ (x : Point n) (i : Fin (n + base.gates)),
      StraightLineCircuit.evalWire (C := builder.circuit) (x := x)
          (builder.liftBase i) =
        StraightLineCircuit.evalWire (C := base) (x := x) i

namespace EvalBuilder

variable {n : ℕ} {base : StraightLineCircuit n}

/-- Underlying circuit carried by the evaluation-aware builder. -/
def circuit (b : EvalBuilder n base) : StraightLineCircuit n :=
  b.builder.circuit

@[simp] lemma circuit_eq (b : EvalBuilder n base) :
    b.circuit = b.builder.circuit := rfl

/-- Lift a base wire into the ambient circuit. -/
def liftBase (b : EvalBuilder n base) (i : Fin (n + base.gates)) :
    Fin (n + b.circuit.gates) :=
  b.builder.liftBase i

@[simp] lemma liftBase_coe (b : EvalBuilder n base)
    (i : Fin (n + base.gates)) : (b.liftBase i : ℕ) = i := rfl

lemma eval_liftBase_eq (b : EvalBuilder n base) (x : Point n)
    (i : Fin (n + base.gates)) :
    StraightLineCircuit.evalWire (C := b.circuit) (x := x) (b.liftBase i) =
      StraightLineCircuit.evalWire (C := base) (x := x) i :=
  b.eval_liftBase x i

/-- Trivial evaluation-aware builder obtained without appending gates. -/
@[simp] def mk (base : StraightLineCircuit n) : EvalBuilder n base :=
  { builder := Builder.mk base
    , eval_liftBase := by intro x i; rfl }

@[simp] lemma mk_liftBase (base : StraightLineCircuit n)
    (i : Fin (n + base.gates)) : (mk (base := base)).liftBase i = i := rfl

@[simp] lemma mk_eval (base : StraightLineCircuit n) (x : Point n)
    (i : Fin (n + base.gates)) :
    StraightLineCircuit.evalWire (C := (mk (base := base)).circuit)
        (x := x) ((mk (base := base)).liftBase i) =
      StraightLineCircuit.evalWire (C := base) (x := x) i := rfl

/-- Lifting base wires after appending a gate agrees with the canonical lift. -/
lemma append_liftBase_eq (b : Builder n base)
    (op : StraightOp (n + b.circuit.gates)) (i : Fin (n + base.gates)) :
    ((b.append op).fst).liftBase i =
      appendFin_lift (b := b) (op := op) i := by
  ext <;> simp [Builder.liftBase, append, appendFin_lift,
    StraightLineCircuit.snoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Appending a gate preserves the evaluation of all base wires. -/
lemma append_preserves_eval (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) (x : Point n)
    (i : Fin (n + base.gates)) :
    StraightLineCircuit.evalWire
        (C := (b.builder.append op).fst.circuit) (x := x)
        (((b.builder.append op).fst).liftBase i) =
      StraightLineCircuit.evalWire (C := base) (x := x) i := by
  have hLift := append_liftBase_eq (b := b.builder) (op := op) i
  have hOld := eval_liftBase_eq (b := b) (x := x) (i := i)
  have := StraightLineCircuit.evalWire_snoc_lift
    (C := b.circuit) (op := op) (x := x) (i := b.builder.liftBase i)
  simp [EvalBuilder.liftBase, circuit, hLift, hOld] at this
  simpa using this

/-- Append a new gate while maintaining the evaluation invariant. -/
def append (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    EvalBuilder n base × Wire n :=
  let raw := b.builder.append op
  let evalPres : EvalBuilder n base :=
    { builder := raw.fst
      , eval_liftBase := by
          intro x i
          simpa using append_preserves_eval (b := b) (op := op) (x := x) (i := i) }
  (evalPres, raw.snd)

@[simp] lemma append_fst_circuit (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    (b.append op).fst.circuit =
      StraightLineCircuit.snoc b.circuit op := rfl

lemma append_eval (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) (x : Point n) :
    let result := b.append op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (result.snd.toFin (n := n)
          (g := result.fst.circuit.gates)
          (by
            have := le_rfl
            simpa [append_fst_circuit] using this)) =
      StraightOp.eval op (fun w =>
        StraightLineCircuit.evalWire (C := b.circuit) (x := x) w) := by
  unfold append
  simp [Builder.append_eval, circuit]

def appendFin (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    EvalBuilder n base × Fin (n + (StraightLineCircuit.snoc b.circuit op).gates) :=
  let result := b.append op
  have hbound : result.snd.bound ≤ result.fst.circuit.gates := by
    simpa using (le_of_eq rfl)
  ( result.fst
  , result.snd.toFin (n := n) (g := result.fst.circuit.gates) hbound )

@[simp] lemma appendFin_gate_eq (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    (b.appendFin op).fst.circuit.gates = b.circuit.gates + 1 := by
  unfold appendFin
  simp [append_fst_circuit, StraightLineCircuit.snoc]

def appendFin_lift (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) :
    let result := b.appendFin op
    Fin (n + b.circuit.gates) → Fin (n + result.fst.circuit.gates) :=
  StraightLineCircuit.Builder.appendFin_lift (b := b.builder) (op := op)

lemma appendFin_eval (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) (x : Point n) :
    let result := b.appendFin op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        result.snd =
      StraightOp.eval op (fun w =>
        StraightLineCircuit.evalWire (C := b.circuit) (x := x) w) := by
  unfold appendFin
  simp [append_eval]

lemma append_evalWire_preserved (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates))
    (w : StraightLineCircuit.Wire n)
    (hw : w.bound ≤ b.circuit.gates) (x : Point n) :
    let result := b.append op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (w.toFin (n := n) (g := result.fst.circuit.gates)
          (by
            -- The appended gate extends the circuit by exactly one position,
            -- hence every previously valid bound remains so after the update.
            have : b.circuit.gates ≤ result.fst.circuit.gates := by
              simpa [result, append_fst_circuit, StraightLineCircuit.snoc]
                using Nat.le_succ b.circuit.gates
            exact Nat.le_trans hw this)) =
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
        (w.toFin (n := n) (g := b.circuit.gates) hw) := by
  classical
  -- Identify the coercion of the wire index through the appended circuit with
  -- the canonical lift provided by `liftWire`.
  have hLift :
      StraightLineCircuit.liftWire (C := b.circuit)
          (w.toFin (n := n) (g := b.circuit.gates) hw) =
        w.toFin (n := n) (g := (b.append op).fst.circuit.gates)
          (by
            have : b.circuit.gates ≤ (b.append op).fst.circuit.gates := by
              simpa [append_fst_circuit, StraightLineCircuit.snoc]
                using Nat.le_succ b.circuit.gates
            exact Nat.le_trans hw this) := by
    ext i
    -- Both sides reduce to the underlying numeric index `w.idx` once coerced
    -- to natural numbers.
    simp [StraightLineCircuit.liftWire, append_fst_circuit,
      StraightLineCircuit.snoc, StraightLineCircuit.Wire.toFin_idx]
  -- Evaluation of the lifted wire agrees with the evaluation in the original
  -- circuit thanks to `evalWire_snoc_lift`.
  simpa [append_fst_circuit, StraightLineCircuit.snoc, hLift]
    using StraightLineCircuit.evalWire_snoc_lift (C := b.circuit)
      (op := op) (x := x)
        (i := w.toFin (n := n) (g := b.circuit.gates) hw)

lemma appendFin_evalWire_preserved (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates))
    (w : StraightLineCircuit.Wire n)
    (hw : w.bound ≤ b.circuit.gates) (x : Point n) :
    let result := b.appendFin op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        (w.toFin (n := n) (g := result.fst.circuit.gates)
          (by
            have : b.circuit.gates ≤ result.fst.circuit.gates := by
              simpa [appendFin, StraightLineCircuit.snoc, append_fst_circuit]
                using Nat.le_succ b.circuit.gates
            exact Nat.le_trans hw this)) =
      StraightLineCircuit.evalWire (C := b.circuit) (x := x)
        (w.toFin (n := n) (g := b.circuit.gates) hw) := by
  classical
  -- Reduce the statement to the corresponding lemma for `append` by unfolding
  -- the definition of `appendFin`.
  unfold appendFin
  -- The helper `append` already provides the required equality; the coercions
  -- introduced by `appendFin` are definitionally identical.
  simpa [append, Builder.append, StraightLineCircuit.snoc]
    using append_evalWire_preserved (b := b) (op := op) (w := w)
      (hw := hw) (x := x)

def appendConstFin (b : EvalBuilder n base) (val : Bool) :
    EvalBuilder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.const val)).gates) :=
  b.appendFin (StraightOp.const val)

def appendNotFin (b : EvalBuilder n base)
    (w : Fin (n + b.circuit.gates)) :
    EvalBuilder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.not w)).gates) :=
  b.appendFin (StraightOp.not w)

def appendAndFin (b : EvalBuilder n base)
    (u v : Fin (n + b.circuit.gates)) :
    EvalBuilder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.and u v)).gates) :=
  b.appendFin (StraightOp.and u v)

def appendOrFin (b : EvalBuilder n base)
    (u v : Fin (n + b.circuit.gates)) :
    EvalBuilder n base × Fin (n + (StraightLineCircuit.snoc b.circuit
      (StraightOp.or u v)).gates) :=
  b.appendFin (StraightOp.or u v)

@[simp] lemma appendConstFin_eval (b : EvalBuilder n base) (val : Bool)
    (x : Point n) :
    let result := b.appendConstFin val
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        result.snd = val := by
  unfold appendConstFin
  simpa using appendFin_eval (b := b) (op := StraightOp.const val) (x := x)

@[simp] lemma appendAndFin_eval (b : EvalBuilder n base)
    (u v : Fin (n + b.circuit.gates)) (x : Point n) :
    let result := b.appendAndFin u v
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        result.snd =
      (StraightLineCircuit.evalWire (C := b.circuit) (x := x) u &&
        StraightLineCircuit.evalWire (C := b.circuit) (x := x) v) := by
  unfold appendAndFin
  simpa using appendFin_eval (b := b) (op := StraightOp.and u v) (x := x)

@[simp] lemma appendOrFin_eval (b : EvalBuilder n base)
    (u v : Fin (n + b.circuit.gates)) (x : Point n) :
    let result := b.appendOrFin u v
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        result.snd =
      (StraightLineCircuit.evalWire (C := b.circuit) (x := x) u ||
        StraightLineCircuit.evalWire (C := b.circuit) (x := x) v) := by
  unfold appendOrFin
  simpa using appendFin_eval (b := b) (op := StraightOp.or u v) (x := x)

lemma appendFin_lift_eval (b : EvalBuilder n base)
    (op : StraightOp (n + b.circuit.gates)) (x : Point n)
    (w : Fin (n + b.circuit.gates)) :
    let result := b.appendFin op
    StraightLineCircuit.evalWire (C := result.fst.circuit) (x := x)
        ((appendFin_lift (b := b) (op := op)) w) =
      StraightLineCircuit.evalWire (C := b.circuit) (x := x) w := by
  unfold appendFin_lift
  have := StraightLineCircuit.evalWire_snoc_lift
    (C := b.circuit) (op := op) (x := x) (i := w)
  simpa using this

end EvalBuilder



end Builder

end StraightLineCircuit
end Boolcube

