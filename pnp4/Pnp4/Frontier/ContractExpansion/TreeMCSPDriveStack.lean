import Pnp4.Frontier.ContractExpansion.TreeMCSPStackFlatten

/-!
# `drive` — D2t-5b: the preorder-streaming driver semantics

The pure semantics of D2t-5's on-tape recursion driver, which reads the certificate **in preorder**
(`encodeCircuitTree`: tag-then-children) and maintains two tape scratch stacks:

* a **control stack** of pending internal nodes — each a `(tag, remaining)` frame, `remaining` = children
  still to be processed; and
* a **value stack** of completed-subtree root WORK-indices.

Reading a leaf token emits its record, pushes its index, and **settles** (notifies the parent); reading an
internal token pushes a `(tag, arity)` frame.  `settle` is the completion cascade: it decrements the top
frame, and when a frame's last child arrives it pops the frame, emits the gate record with the children's
indices (popped off the value stack), pushes the new index, and recurses to the grandparent.

Unlike `runStack` (#1590, which executes the *already-sequenced* postorder step program `toSteps`), `drive`
**produces** the postorder order itself from the preorder stream via the control stack — exactly what the
on-tape machine does.  Proven correct against the structural `flattenAt`:

* `drive_preorder` — running `c`'s preorder appends `flattenAt out.length c` to WORK and settles `c`'s root
  index `out.length + c.size - 1` into the control stack (induction on the tree).
* `driveWORK_eq_flatten` — `(drive (preorder c) ([], [], [])).1 = (flatten c).gates`: the driver's WORK is
  the postorder flatten, control + value stacks empty/singleton at the end.

**Progress classification (AGENTS.md): Infrastructure** — a pure transcoder-driver spec proven against the
verified `flattenAt`; builds no machine and proves no separation.  Standard triple only.  **No `P ≠ NP`
claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- An internal gate tag (the certificate's `not`/`and`/`or`), with its arity. -/
inductive ITag where
  | tnot | tand | tor
  deriving DecidableEq

/-- Number of children an internal node of this tag has. -/
def ITag.arity : ITag → Nat
  | .tnot => 1
  | .tand => 2
  | .tor => 2

/-- A preorder certificate token: a leaf gate, or an internal node tag (children follow in preorder). -/
inductive PreToken (n : Nat) where
  | leaf : SLGate n → PreToken n
  | node : ITag → PreToken n

/-- **Settle** the completion cascade.  Called when a subtree has just completed (its root index sits on
top of the value stack `val`): decrement the top control frame; when its last child has arrived
(`remaining = 1`), pop it, emit the internal gate with the children's indices (off `val`), push the new
gate's index `out.length`, and recurse to the next parent.  Structurally recursive on the control stack. -/
def settle {n : Nat} (out : List (SLGate n)) :
    List (ITag × Nat) → List Nat → (List (SLGate n) × List (ITag × Nat) × List Nat)
  | [], val => (out, [], val)
  | (tag, rem) :: ctrl, val =>
    if rem = 1 then
      match tag, val with
      | ITag.tnot, i :: vs => settle (out ++ [SLGate.notGate i]) ctrl (out.length :: vs)
      | ITag.tand, i2 :: i1 :: vs => settle (out ++ [SLGate.andGate i1 i2]) ctrl (out.length :: vs)
      | ITag.tor, i2 :: i1 :: vs => settle (out ++ [SLGate.orGate i1 i2]) ctrl (out.length :: vs)
      | _, val => (out, ctrl, val)
    else
      (out, (tag, rem - 1) :: ctrl, val)

/-- Process one preorder token against the driver state `(WORK, control stack, value stack)`. -/
def processToken {n : Nat} :
    (List (SLGate n) × List (ITag × Nat) × List Nat) → PreToken n →
      (List (SLGate n) × List (ITag × Nat) × List Nat)
  | (out, ctrl, val), PreToken.leaf g => settle (out ++ [g]) ctrl (out.length :: val)
  | (out, ctrl, val), PreToken.node tag => (out, (tag, tag.arity) :: ctrl, val)

/-- Run the driver over a preorder token stream. -/
def drive {n : Nat} (tokens : List (PreToken n))
    (st : List (SLGate n) × List (ITag × Nat) × List Nat) :
    List (SLGate n) × List (ITag × Nat) × List Nat :=
  tokens.foldl processToken st

/-- The preorder serialization of a circuit tree as driver tokens (tag-then-children). -/
def preorder {n : Nat} : CircuitTree n → List (PreToken n)
  | .input i => [PreToken.leaf (SLGate.input i)]
  | .const b => [PreToken.leaf (SLGate.const b)]
  | .not c => PreToken.node ITag.tnot :: preorder c
  | .and a b => PreToken.node ITag.tand :: (preorder a ++ preorder b)
  | .or a b => PreToken.node ITag.tor :: (preorder a ++ preorder b)

/-- **The driver invariant.**  Running `c`'s preorder appends exactly `flattenAt out.length c` to WORK and
then settles `c`'s root index `out.length + c.size - 1` into the control stack.  Induction on the tree:
internal nodes push a frame, recurse into children (the first child's completion decrements the frame; the
last child's completion emits the gate), so the net effect on WORK and the settle-into-parent matches a
leaf's. -/
theorem drive_preorder {n : Nat} (c : CircuitTree n) :
    ∀ (out : List (SLGate n)) (ctrl : List (ITag × Nat)) (val : List Nat),
      drive (preorder c) (out, ctrl, val)
        = settle (out ++ CircuitTree.flattenAt out.length c) ctrl
            ((out.length + c.size - 1) :: val) := by
  induction c with
  | input i =>
      intro out ctrl val
      simp [preorder, drive, processToken, CircuitTree.flattenAt, CircuitTree.size]
  | const b =>
      intro out ctrl val
      simp [preorder, drive, processToken, CircuitTree.flattenAt, CircuitTree.size]
  | not c ih =>
      intro out ctrl val
      have hc : 1 ≤ c.size := CircuitTree.one_le_size c
      rw [show preorder (CircuitTree.not c) = PreToken.node ITag.tnot :: preorder c from rfl,
        drive, List.foldl_cons,
        show processToken (out, ctrl, val) (PreToken.node ITag.tnot)
            = (out, (ITag.tnot, 1) :: ctrl, val) from rfl,
        show (preorder c).foldl processToken (out, (ITag.tnot, 1) :: ctrl, val)
            = drive (preorder c) (out, (ITag.tnot, 1) :: ctrl, val) from rfl,
        ih out ((ITag.tnot, 1) :: ctrl) val]
      -- settle the (tnot,1) frame: emit notGate over c's root index
      simp only [settle, CircuitTree.flattenAt, CircuitTree.size, List.length_append,
        CircuitTree.flattenAt_length, List.append_assoc, if_true]
      congr 2
  | and a b iha ihb =>
      intro out ctrl val
      have ha : 1 ≤ a.size := CircuitTree.one_le_size a
      have hb : 1 ≤ b.size := CircuitTree.one_le_size b
      rw [show preorder (CircuitTree.and a b)
            = PreToken.node ITag.tand :: (preorder a ++ preorder b) from rfl,
        drive, List.foldl_cons,
        show processToken (out, ctrl, val) (PreToken.node ITag.tand)
            = (out, (ITag.tand, 2) :: ctrl, val) from rfl,
        List.foldl_append,
        show (preorder a).foldl processToken (out, (ITag.tand, 2) :: ctrl, val)
            = drive (preorder a) (out, (ITag.tand, 2) :: ctrl, val) from rfl,
        iha out ((ITag.tand, 2) :: ctrl) val]
      -- settle the (tand,2) frame: just decrement to (tand,1)
      rw [show settle (out ++ CircuitTree.flattenAt out.length a) ((ITag.tand, 2) :: ctrl)
              ((out.length + a.size - 1) :: val)
            = (out ++ CircuitTree.flattenAt out.length a, (ITag.tand, 1) :: ctrl,
                (out.length + a.size - 1) :: val) from rfl,
        show (preorder b).foldl processToken
              (out ++ CircuitTree.flattenAt out.length a, (ITag.tand, 1) :: ctrl,
                (out.length + a.size - 1) :: val)
            = drive (preorder b) (out ++ CircuitTree.flattenAt out.length a, (ITag.tand, 1) :: ctrl,
                (out.length + a.size - 1) :: val) from rfl,
        ihb (out ++ CircuitTree.flattenAt out.length a) ((ITag.tand, 1) :: ctrl)
          ((out.length + a.size - 1) :: val)]
      simp only [settle, CircuitTree.flattenAt, CircuitTree.size, List.length_append,
        CircuitTree.flattenAt_length, List.append_assoc, if_true]
      congr 2
  | or a b iha ihb =>
      intro out ctrl val
      have ha : 1 ≤ a.size := CircuitTree.one_le_size a
      have hb : 1 ≤ b.size := CircuitTree.one_le_size b
      rw [show preorder (CircuitTree.or a b)
            = PreToken.node ITag.tor :: (preorder a ++ preorder b) from rfl,
        drive, List.foldl_cons,
        show processToken (out, ctrl, val) (PreToken.node ITag.tor)
            = (out, (ITag.tor, 2) :: ctrl, val) from rfl,
        List.foldl_append,
        show (preorder a).foldl processToken (out, (ITag.tor, 2) :: ctrl, val)
            = drive (preorder a) (out, (ITag.tor, 2) :: ctrl, val) from rfl,
        iha out ((ITag.tor, 2) :: ctrl) val]
      rw [show settle (out ++ CircuitTree.flattenAt out.length a) ((ITag.tor, 2) :: ctrl)
              ((out.length + a.size - 1) :: val)
            = (out ++ CircuitTree.flattenAt out.length a, (ITag.tor, 1) :: ctrl,
                (out.length + a.size - 1) :: val) from rfl,
        show (preorder b).foldl processToken
              (out ++ CircuitTree.flattenAt out.length a, (ITag.tor, 1) :: ctrl,
                (out.length + a.size - 1) :: val)
            = drive (preorder b) (out ++ CircuitTree.flattenAt out.length a, (ITag.tor, 1) :: ctrl,
                (out.length + a.size - 1) :: val) from rfl,
        ihb (out ++ CircuitTree.flattenAt out.length a) ((ITag.tor, 1) :: ctrl)
          ((out.length + a.size - 1) :: val)]
      simp only [settle, CircuitTree.flattenAt, CircuitTree.size, List.length_append,
        CircuitTree.flattenAt_length, List.append_assoc, if_true]
      congr 2

/-- The driver's WORK output: run the preorder from empty WORK and empty stacks. -/
def driveWORK {n : Nat} (c : CircuitTree n) : List (SLGate n) :=
  (drive (preorder c) ([], [], [])).1

/-- **D2t-5b driver correctness (pure).**  The preorder-streaming driver produces exactly the postorder
flattened gate list — the WORK target the on-tape D2t-5b loop must realise. -/
theorem driveWORK_eq_flatten {n : Nat} (c : CircuitTree n) :
    driveWORK c = (CircuitTree.flatten c).gates := by
  have h := drive_preorder c [] [] []
  -- settle with empty control stack returns WORK unchanged
  unfold driveWORK
  rw [h]
  simp [settle, CircuitTree.flatten]

end ContractExpansion
end Frontier
end Pnp4
