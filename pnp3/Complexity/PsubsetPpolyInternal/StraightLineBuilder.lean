import Complexity.PsubsetPpolyInternal.StraightLine

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace StraightLine

/-!
Minimal straight-line builder primitives used by the internal simulation port.
-/

variable {n : Nat}

abbrev Op := GateOp
abbrev Ckt (n : Nat) := Circuit n

structure Wire (n : Nat) where
  idx : Nat
  bound : Nat
  bound_lt : idx < n + bound

namespace Wire

def ofFin {n g : Nat} (w : Fin (n + g)) : Wire n where
  idx := w
  bound := g
  bound_lt := by simpa using w.isLt

def toFin {n : Nat} (w : Wire n) {g : Nat} (hg : w.bound ≤ g) : Fin (n + g) :=
  ⟨w.idx, by
    have hle : n + w.bound ≤ n + g := Nat.add_le_add_left hg n
    exact Nat.lt_of_lt_of_le w.bound_lt hle⟩

@[simp] lemma toFin_ofFin {n g : Nat} (w : Fin (n + g)) :
    (ofFin w).toFin (g := g) (Nat.le_refl g) = w := by
  ext
  rfl

@[simp] lemma toFin_idx {n : Nat} (w : Wire n) {g : Nat} (hg : w.bound ≤ g) :
    ((w.toFin (g := g) hg : Fin (n + g)) : Nat) = w.idx := rfl

end Wire



structure BuildCtx (n : Nat) (base : Ckt n) where
  circuit : Ckt n
  base_le : base.gates ≤ circuit.gates

namespace BuildCtx

variable {base : Ckt n}

@[simp] def init (base : Ckt n) : BuildCtx n base where
  circuit := base
  base_le := le_rfl

def liftBase (b : BuildCtx n base) (i : Fin (n + base.gates)) :
    Fin (n + b.circuit.gates) :=
  ⟨i, by
    have hi : (i : Nat) < n + base.gates := i.isLt
    have hle : n + base.gates ≤ n + b.circuit.gates := Nat.add_le_add_left b.base_le n
    exact Nat.lt_of_lt_of_le hi hle⟩

def append (b : BuildCtx n base) (op : Op (n + b.circuit.gates)) :
    BuildCtx n base × Wire n :=
  let C' := snoc b.circuit op
  let b' : BuildCtx n base :=
    { circuit := C'
      base_le := Nat.le_trans b.base_le (Nat.le_of_lt (Nat.lt_succ_self _)) }
  let idx := n + b.circuit.gates
  let bound := C'.gates
  have hlt : idx < n + bound := by
    have : n + b.circuit.gates < n + (b.circuit.gates + 1) := Nat.lt_succ_self _
    simpa [idx, bound, C', snoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  (b', { idx := idx, bound := bound, bound_lt := hlt })

@[simp] lemma append_fst_circuit (b : BuildCtx n base)
    (op : Op (n + b.circuit.gates)) :
    (b.append op).fst.circuit = snoc b.circuit op := rfl

def appendFin (b : BuildCtx n base) (op : Op (n + b.circuit.gates)) :
    BuildCtx n base × Fin (n + (snoc b.circuit op).gates) :=
  let r := b.append op
  have hbound : r.snd.bound ≤ r.fst.circuit.gates := by
    dsimp [r, append]
    simp [snoc]
  (r.fst, r.snd.toFin (g := r.fst.circuit.gates) hbound)

@[simp] lemma appendFin_gate_eq (b : BuildCtx n base)
    (op : Op (n + b.circuit.gates)) :
    (b.appendFin op).fst.circuit.gates = b.circuit.gates + 1 := by
  unfold appendFin
  simp [append_fst_circuit, snoc]

def appendFin_lift (b : BuildCtx n base) (op : Op (n + b.circuit.gates)) :
    Fin (n + b.circuit.gates) → Fin (n + (b.appendFin op).fst.circuit.gates) := by
  intro w
  have hg : (b.appendFin op).fst.circuit.gates = b.circuit.gates + 1 :=
    appendFin_gate_eq (b := b) (op := op)
  simpa [hg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (liftWire (C := b.circuit) w)

def appendConstFin (b : BuildCtx n base) (val : Bool) :
    BuildCtx n base × Fin (n + (snoc b.circuit (.const val)).gates) :=
  b.appendFin (.const val)

def appendNotFin (b : BuildCtx n base) (w : Fin (n + b.circuit.gates)) :
    BuildCtx n base × Fin (n + (snoc b.circuit (.not w)).gates) :=
  b.appendFin (.not w)

def appendAndFin (b : BuildCtx n base)
    (u v : Fin (n + b.circuit.gates)) :
    BuildCtx n base × Fin (n + (snoc b.circuit (.and u v)).gates) :=
  b.appendFin (.and u v)

def appendOrFin (b : BuildCtx n base)
    (u v : Fin (n + b.circuit.gates)) :
    BuildCtx n base × Fin (n + (snoc b.circuit (.or u v)).gates) :=
  b.appendFin (.or u v)

end BuildCtx

structure EvalBuildCtx (n : Nat) (base : Ckt n) where
  ctx : BuildCtx n base
  eval_liftBase :
    ∀ (x : Boolcube.Point n) (i : Fin (n + base.gates)),
      evalWire (C := ctx.circuit) (x := x) (ctx.liftBase i) =
        evalWire (C := base) (x := x) i

namespace EvalBuildCtx

variable {base : Ckt n}

@[simp] def init (base : Ckt n) : EvalBuildCtx n base where
  ctx := BuildCtx.init base
  eval_liftBase := by
    intro x i
    rfl

def circuit (b : EvalBuildCtx n base) : Ckt n := b.ctx.circuit

def liftBase (b : EvalBuildCtx n base) (i : Fin (n + base.gates)) :
    Fin (n + b.circuit.gates) :=
  b.ctx.liftBase i

/--
Append with explicit semantic preservation proof for old wires.
This isolates the only hard lemma needed from circuit semantics (`snoc`-preserve).
-/
def appendWith (b : EvalBuildCtx n base)
    (op : Op (n + b.circuit.gates))
    (hPres :
      ∀ (x : Boolcube.Point n) (w : Fin (n + b.circuit.gates)),
        evalWire (C := snoc b.circuit op) (x := x) (liftWire (C := b.circuit) w) =
          evalWire (C := b.circuit) (x := x) w) :
    EvalBuildCtx n base × Fin (n + (snoc b.circuit op).gates) := by
  let r := b.ctx.appendFin op
  refine ⟨{
    ctx := r.fst
    eval_liftBase := ?_
  }, r.snd⟩
  intro x i
  have hLift :
      BuildCtx.appendFin_lift (b := b.ctx) (op := op) (b.ctx.liftBase i) =
        r.fst.liftBase i := by
    ext
    simp [r, BuildCtx.appendFin_lift, BuildCtx.liftBase, liftWire,
      BuildCtx.appendFin_gate_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hOld := b.eval_liftBase x i
  have hPres' := hPres x (b.ctx.liftBase i)
  simpa [r, circuit, liftBase, hLift] using hPres'.trans hOld

end EvalBuildCtx

end StraightLine
end PsubsetPpoly
end Internal
end Pnp3
