import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStepTerminates

/-!
# `DriveState.Pending` — D2t-5b (Block A1b): the reachable-state coherence invariant

The small-step driver's *raw* terminal condition is deliberately permissive (`TreeMCSPDriveStep`), and the
strong tape invariant's cheap coherence clause (`driverStrongInv`, A1a) is only pointwise.  The on-tape
loop, however, needs **run-trace** facts: its sink test is "*in the settle phase the control stack is
empty*" (control-stack emptiness is one cell of the stack's pointer field — whereas "the certificate is
exhausted" is *not* detectable on a `Bool` tape, where blank cells are indistinguishable from a leaf tag).
For that test to be sound the driver must satisfy, at every reachable state, the **pending-forest
decomposition**: the unread tokens are exactly the preorders of the still-pending subtrees, grouped by the
control-stack frames, with the completed-children indices sitting on the value stack in matching counts.

This module defines that decomposition and proves it is an invariant of the run:

* `PendingFrames` — the below-top frames: each `(tag, rem)` frame has `rem = |pending| + 1` (the `+1` is
  the in-progress child occupying one slot) and `|completed on val| + |pending| + 1 = tag.arity`.
* `PendingTop` — the whole-state judgment: an empty control stack means the tokens are a single full
  preorder (reading) or nothing (settling — **the sink-soundness base case**, with the completed root's
  index on the value stack); a top frame has `rem = |pending| + (1 if settling)` and
  `|completed| + |pending| = tag.arity`.
* `pending_init` / `pending_step` / `pending_iterate` — the invariant holds initially and is preserved by
  every `DriveState.step` (the underflow arms are *excluded*: the value stack always matches the popped
  frame's arity exactly).
* **`driver_sink_sound`** — at any reachable state, `settling ∧ ctrl = [] → toks = []`: the machine sink
  test never fires early.  (`driver_sink_val_ne_nil`: and the completed root's index is on the value
  stack.)
* **`driver_sink_exists`** — the run *reaches* the sink, within `3 · c.size` steps, **with the postorder
  flatten already in WORK**: `∃ k < 3·c.size, settling ∧ ctrl = [] ∧ toks = [] ∧ out = (flatten c).gates`.
  (The only reachable transition into the pure terminal state is the settle-empty arm, which fixes
  everything but the flag — so stopping at the sink loses nothing.)
* `pendingFrames_rem_bounds` — every below-top frame has `1 ≤ rem ≤ arity ≤ 2`: the on-tape frame is a
  **fixed-width** (≤ 6-cell) object, so the settle decrement is a bounded rewrite (consumed by A4b).

**Progress classification (AGENTS.md): Infrastructure** — a pure reachability invariant for the verified
small-step driver; builds no machine and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The preorder serialization of a forest: the trees' preorders concatenated. -/
def preorderForest {n : Nat} : List (CircuitTree n) → List (PreToken n)
  | [] => []
  | t :: ts => preorder t ++ preorderForest ts

@[simp] theorem preorderForest_nil {n : Nat} : preorderForest ([] : List (CircuitTree n)) = [] := rfl

@[simp] theorem preorderForest_cons {n : Nat} (t : CircuitTree n) (ts : List (CircuitTree n)) :
    preorderForest (t :: ts) = preorder t ++ preorderForest ts := rfl

/-- A preorder stream is never empty (one token per node, `≥ 1` node). -/
theorem preorder_ne_nil {n : Nat} (t : CircuitTree n) : preorder t ≠ [] := by
  intro h
  have hlen := preorder_length t
  have hpos := CircuitTree.one_le_size t
  rw [h] at hlen
  simp at hlen
  omega

/-- A list with a nonempty left factor is nonempty. -/
theorem append_left_ne_nil {α : Type _} {xs ys : List α} (h : xs ≠ []) : xs ++ ys ≠ [] := by
  cases xs with
  | nil => exact absurd rfl h
  | cons a as => simp

/-- **The below-top frames' pending decomposition.**  Reading the control stack downward from just below
the top: each frame `(tag, rem)` has one child **in progress** (the activity above it — the `+1`), `ts`
pending (not-yet-started) subtrees whose preorders open the corresponding token segment, and `vs`
completed-children indices on the value stack, with `|vs| + |ts| + 1 = tag.arity`; below the last frame no
tokens remain (`nil`). -/
inductive PendingFrames {n : Nat} : List (ITag × Nat) → List (PreToken n) → List Nat → Prop
  | nil (val : List Nat) : PendingFrames [] [] val
  | frame (tag : ITag) (ctrl' : List (ITag × Nat)) (ts : List (CircuitTree n))
      (rest : List (PreToken n)) (vs val' : List Nat)
      (harity : vs.length + ts.length + 1 = tag.arity)
      (hdeep : PendingFrames ctrl' rest val') :
      PendingFrames ((tag, ts.length + 1) :: ctrl') (preorderForest ts ++ rest) (vs ++ val')

/-- **The whole-state pending judgment.**  With an empty control stack: reading means the tokens are
nothing or one full preorder (the initial state); settling means the completed subtree was the **root** —
no tokens remain and its index tops the value stack (the sink-soundness base case).  With a top frame
`(tag, rem)`: `rem` counts the pending subtrees plus the just-completed one while settling
(`rem = |ts| + 1`) and exactly the pending ones while reading (`rem = |ts|`, necessarily `≥ 1` — the next
token always opens the top frame's next subtree); completed-children indices `vs` top the value stack with
`|vs| + |ts| = tag.arity`; the deeper frames satisfy `PendingFrames`. -/
def PendingTop {n : Nat} : Bool → List (ITag × Nat) → List (PreToken n) → List Nat → Prop
  | false, [], toks, _ => toks = [] ∨ ∃ t : CircuitTree n, toks = preorder t
  | true, [], toks, val => toks = [] ∧ val ≠ []
  | occupied, (tag, rem) :: ctrl', toks, val =>
      ∃ (ts : List (CircuitTree n)) (rest : List (PreToken n)) (vs val' : List Nat),
        rem = ts.length + (if occupied then 1 else 0)
        ∧ 1 ≤ rem
        ∧ vs.length + ts.length = tag.arity
        ∧ toks = preorderForest ts ++ rest
        ∧ val = vs ++ val'
        ∧ PendingFrames ctrl' rest val'

/-- The driver coherence invariant: the micro-state satisfies the pending-forest decomposition. -/
def DriveState.Pending {n : Nat} (s : DriveState n) : Prop :=
  PendingTop s.settling s.ctrl s.toks s.val

/-- The invariant holds at the initial state: the whole certificate is one full preorder. -/
theorem pending_init {n : Nat} (c : CircuitTree n) :
    (⟨preorder c, [], [], [], false⟩ : DriveState n).Pending :=
  Or.inr ⟨c, rfl⟩

/-- A reading state whose next token is an internal-node tag has more tokens behind it (the node's
children follow in preorder) — so a node read never exhausts the certificate. -/
theorem pending_reading_node {n : Nat} {ctrl : List (ITag × Nat)} {tag : ITag}
    {toks' : List (PreToken n)} {val : List Nat}
    (hp : PendingTop false ctrl (PreToken.node tag :: toks') val) : toks' ≠ [] := by
  cases ctrl with
  | nil =>
      rcases hp with h | ⟨t, ht⟩
      · exact absurd h (List.cons_ne_nil _ _)
      · cases t with
        | input i => exact absurd ht (by simp [preorder])
        | const b => exact absurd ht (by simp [preorder])
        | not c =>
            rw [show preorder (CircuitTree.not c) = PreToken.node ITag.tnot :: preorder c from rfl] at ht
            obtain ⟨-, htoks⟩ := List.cons.inj ht
            rw [htoks]
            exact preorder_ne_nil c
        | and a b =>
            rw [show preorder (CircuitTree.and a b)
                = PreToken.node ITag.tand :: (preorder a ++ preorder b) from rfl] at ht
            obtain ⟨-, htoks⟩ := List.cons.inj ht
            rw [htoks]
            exact append_left_ne_nil (preorder_ne_nil a)
        | or a b =>
            rw [show preorder (CircuitTree.or a b)
                = PreToken.node ITag.tor :: (preorder a ++ preorder b) from rfl] at ht
            obtain ⟨-, htoks⟩ := List.cons.inj ht
            rw [htoks]
            exact append_left_ne_nil (preorder_ne_nil a)
  | cons f ctrl' =>
      obtain ⟨tag₀, rem₀⟩ := f
      obtain ⟨ts, rest, vs, val', hrem, hpos, -, htoks, -, -⟩ := hp
      simp only [if_neg Bool.false_ne_true] at hrem
      cases ts with
      | nil => simp at hrem; omega
      | cons t₁ ts'' =>
          rw [preorderForest_cons, List.append_assoc] at htoks
          cases t₁ with
          | input i => exact absurd htoks (by simp [preorder])
          | const b => exact absurd htoks (by simp [preorder])
          | not c =>
              rw [show preorder (CircuitTree.not c)
                  = PreToken.node ITag.tnot :: preorder c from rfl, List.cons_append] at htoks
              obtain ⟨-, htoks'⟩ := List.cons.inj htoks
              rw [htoks']
              exact append_left_ne_nil (preorder_ne_nil c)
          | and a b =>
              rw [show preorder (CircuitTree.and a b)
                  = PreToken.node ITag.tand :: (preorder a ++ preorder b) from rfl,
                List.cons_append, List.append_assoc] at htoks
              obtain ⟨-, htoks'⟩ := List.cons.inj htoks
              rw [htoks']
              exact append_left_ne_nil (preorder_ne_nil a)
          | or a b =>
              rw [show preorder (CircuitTree.or a b)
                  = PreToken.node ITag.tor :: (preorder a ++ preorder b) from rfl,
                List.cons_append, List.append_assoc] at htoks
              obtain ⟨-, htoks'⟩ := List.cons.inj htoks
              rw [htoks']
              exact append_left_ne_nil (preorder_ne_nil a)

/-- **The pending decomposition is preserved by every micro-step.**  Case analysis on the action; the
underflow arms cannot fire (the value stack always carries exactly the popped frame's arity). -/
theorem pending_step {n : Nat} (s : DriveState n) (h : s.Pending) : s.step.Pending := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  replace h : PendingTop settling ctrl toks val := h
  cases settling with
  | false =>
      cases toks with
      | nil => exact h
      | cons tok toks' =>
          cases ctrl with
          | nil =>
              rcases h with habs | ⟨t, ht⟩
              · exact absurd habs (List.cons_ne_nil _ _)
              · cases t with
                | input i =>
                    obtain ⟨htok, htoks'⟩ := List.cons.inj ht
                    subst htok; subst htoks'
                    show PendingTop true [] [] (out.length :: val)
                    exact ⟨rfl, List.cons_ne_nil _ _⟩
                | const b =>
                    obtain ⟨htok, htoks'⟩ := List.cons.inj ht
                    subst htok; subst htoks'
                    show PendingTop true [] [] (out.length :: val)
                    exact ⟨rfl, List.cons_ne_nil _ _⟩
                | not c =>
                    rw [show preorder (CircuitTree.not c)
                        = PreToken.node ITag.tnot :: preorder c from rfl] at ht
                    obtain ⟨htok, htoks'⟩ := List.cons.inj ht
                    subst htok; subst htoks'
                    show PendingTop false [(ITag.tnot, ITag.arity ITag.tnot)] (preorder c) val
                    exact ⟨[c], [], [], val, by simp [ITag.arity], by simp [ITag.arity],
                      by simp [ITag.arity], by simp, by simp, PendingFrames.nil val⟩
                | and a b =>
                    rw [show preorder (CircuitTree.and a b)
                        = PreToken.node ITag.tand :: (preorder a ++ preorder b) from rfl] at ht
                    obtain ⟨htok, htoks'⟩ := List.cons.inj ht
                    subst htok; subst htoks'
                    show PendingTop false [(ITag.tand, ITag.arity ITag.tand)]
                      (preorder a ++ preorder b) val
                    exact ⟨[a, b], [], [], val, by simp [ITag.arity], by simp [ITag.arity],
                      by simp [ITag.arity], by simp, by simp, PendingFrames.nil val⟩
                | or a b =>
                    rw [show preorder (CircuitTree.or a b)
                        = PreToken.node ITag.tor :: (preorder a ++ preorder b) from rfl] at ht
                    obtain ⟨htok, htoks'⟩ := List.cons.inj ht
                    subst htok; subst htoks'
                    show PendingTop false [(ITag.tor, ITag.arity ITag.tor)]
                      (preorder a ++ preorder b) val
                    exact ⟨[a, b], [], [], val, by simp [ITag.arity], by simp [ITag.arity],
                      by simp [ITag.arity], by simp, by simp, PendingFrames.nil val⟩
          | cons f ctrl' =>
              obtain ⟨tag₀, rem₀⟩ := f
              obtain ⟨ts, rest, vs, val', hrem, hpos, harity, htoks, hval, hframes⟩ := h
              simp only [if_neg Bool.false_ne_true] at hrem
              cases ts with
              | nil => simp at hrem; omega
              | cons t₁ ts'' =>
                  simp only [List.length_cons] at hrem harity
                  rw [preorderForest_cons, List.append_assoc] at htoks
                  cases t₁ with
                  | input i =>
                      obtain ⟨htok, htoks'⟩ := List.cons.inj htoks
                      subst htok; subst htoks'
                      show PendingTop true ((tag₀, rem₀) :: ctrl')
                        (preorderForest ts'' ++ rest) (out.length :: val)
                      refine ⟨ts'', rest, out.length :: vs, val', by simp; omega, by omega,
                        by simp only [List.length_cons]; omega, rfl, by simp [hval], hframes⟩
                  | const b =>
                      obtain ⟨htok, htoks'⟩ := List.cons.inj htoks
                      subst htok; subst htoks'
                      show PendingTop true ((tag₀, rem₀) :: ctrl')
                        (preorderForest ts'' ++ rest) (out.length :: val)
                      refine ⟨ts'', rest, out.length :: vs, val', by simp; omega, by omega,
                        by simp only [List.length_cons]; omega, rfl, by simp [hval], hframes⟩
                  | not c =>
                      rw [show preorder (CircuitTree.not c)
                          = PreToken.node ITag.tnot :: preorder c from rfl, List.cons_append] at htoks
                      obtain ⟨htok, htoks'⟩ := List.cons.inj htoks
                      subst htok; subst htoks'
                      show PendingTop false ((ITag.tnot, ITag.arity ITag.tnot) :: (tag₀, rem₀) :: ctrl')
                        (preorder c ++ (preorderForest ts'' ++ rest)) val
                      refine ⟨[c], preorderForest ts'' ++ rest, [], val,
                        by simp [ITag.arity], by simp [ITag.arity], by simp [ITag.arity],
                        by simp, by simp, ?_⟩
                      rw [hval, show rem₀ = ts''.length + 1 by simpa using hrem]
                      exact PendingFrames.frame tag₀ ctrl' ts'' rest vs val'
                        (by omega) hframes
                  | and a b =>
                      rw [show preorder (CircuitTree.and a b)
                          = PreToken.node ITag.tand :: (preorder a ++ preorder b) from rfl,
                        List.cons_append] at htoks
                      obtain ⟨htok, htoks'⟩ := List.cons.inj htoks
                      subst htok; subst htoks'
                      show PendingTop false ((ITag.tand, ITag.arity ITag.tand) :: (tag₀, rem₀) :: ctrl')
                        ((preorder a ++ preorder b) ++ (preorderForest ts'' ++ rest)) val
                      refine ⟨[a, b], preorderForest ts'' ++ rest, [], val,
                        by simp [ITag.arity], by simp [ITag.arity], by simp [ITag.arity],
                        by simp, by simp, ?_⟩
                      rw [hval, show rem₀ = ts''.length + 1 by simpa using hrem]
                      exact PendingFrames.frame tag₀ ctrl' ts'' rest vs val'
                        (by omega) hframes
                  | or a b =>
                      rw [show preorder (CircuitTree.or a b)
                          = PreToken.node ITag.tor :: (preorder a ++ preorder b) from rfl,
                        List.cons_append] at htoks
                      obtain ⟨htok, htoks'⟩ := List.cons.inj htoks
                      subst htok; subst htoks'
                      show PendingTop false ((ITag.tor, ITag.arity ITag.tor) :: (tag₀, rem₀) :: ctrl')
                        ((preorder a ++ preorder b) ++ (preorderForest ts'' ++ rest)) val
                      refine ⟨[a, b], preorderForest ts'' ++ rest, [], val,
                        by simp [ITag.arity], by simp [ITag.arity], by simp [ITag.arity],
                        by simp, by simp, ?_⟩
                      rw [hval, show rem₀ = ts''.length + 1 by simpa using hrem]
                      exact PendingFrames.frame tag₀ ctrl' ts'' rest vs val'
                        (by omega) hframes
  | true =>
      cases ctrl with
      | nil =>
          obtain ⟨htoks, -⟩ := h
          subst htoks
          show PendingTop false [] [] val
          exact Or.inl rfl
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          obtain ⟨ts, rest, vs, val', hrem, hpos, harity, htoks, hval, hframes⟩ := h
          cases ts with
          | cons t₁ ts'' =>
              -- `rem = |ts| + 1 ≥ 2`: the decrement arm.
              have hne : rem ≠ 1 := by simp at hrem; omega
              have hstep : DriveState.step ⟨toks, out, (tag, rem) :: ctrl', val, true⟩
                  = ⟨toks, out, (tag, rem - 1) :: ctrl', val, false⟩ := by
                simp [DriveState.step, hne]
              rw [hstep]
              show PendingTop false ((tag, rem - 1) :: ctrl') toks val
              refine ⟨t₁ :: ts'', rest, vs, val', by simp at hrem ⊢; omega, by simp at hrem ⊢; omega,
                harity, htoks, hval, hframes⟩
          | nil =>
              -- `rem = 1`: the pop-emit arm; the value stack carries exactly `arity` entries.
              have hrem1 : rem = 1 := by simpa using hrem
              subst hrem1
              simp only [preorderForest_nil, List.nil_append] at htoks
              subst htoks
              cases tag with
              | tnot =>
                  have hvs : vs.length = 1 := by simpa [ITag.arity] using harity
                  obtain ⟨v, hv⟩ : ∃ v, vs = [v] := by
                    cases vs with
                    | nil => simp at hvs
                    | cons a as =>
                        cases as with
                        | nil => exact ⟨a, rfl⟩
                        | cons b bs => simp at hvs
                  subst hv
                  rw [hval]
                  have hstep : DriveState.step ⟨toks, out, (ITag.tnot, 1) :: ctrl', [v] ++ val', true⟩
                      = ⟨toks, out ++ [SLGate.notGate v], ctrl', out.length :: val', true⟩ := by
                    simp [DriveState.step]
                  rw [hstep]
                  show PendingTop true ctrl' toks (out.length :: val')
                  cases hframes with
                  | nil => exact ⟨rfl, List.cons_ne_nil _ _⟩
                  | frame tag' ctrl'' ts' rest' vs' val'' harity' hdeep' =>
                      exact ⟨ts', rest', out.length :: vs', val'', by simp, by omega,
                        by simp at harity' ⊢; omega, rfl, by simp, hdeep'⟩
              | tand =>
                  have hvs : vs.length = 2 := by simpa [ITag.arity] using harity
                  obtain ⟨x, y, hv⟩ : ∃ x y, vs = [x, y] := by
                    cases vs with
                    | nil => simp at hvs
                    | cons a as =>
                        cases as with
                        | nil => simp at hvs
                        | cons b bs =>
                            cases bs with
                            | nil => exact ⟨a, b, rfl⟩
                            | cons c cs => simp at hvs
                  subst hv
                  rw [hval]
                  have hstep : DriveState.step
                      ⟨toks, out, (ITag.tand, 1) :: ctrl', [x, y] ++ val', true⟩
                      = ⟨toks, out ++ [SLGate.andGate y x], ctrl', out.length :: val', true⟩ := by
                    simp [DriveState.step]
                  rw [hstep]
                  show PendingTop true ctrl' toks (out.length :: val')
                  cases hframes with
                  | nil => exact ⟨rfl, List.cons_ne_nil _ _⟩
                  | frame tag' ctrl'' ts' rest' vs' val'' harity' hdeep' =>
                      exact ⟨ts', rest', out.length :: vs', val'', by simp, by omega,
                        by simp at harity' ⊢; omega, rfl, by simp, hdeep'⟩
              | tor =>
                  have hvs : vs.length = 2 := by simpa [ITag.arity] using harity
                  obtain ⟨x, y, hv⟩ : ∃ x y, vs = [x, y] := by
                    cases vs with
                    | nil => simp at hvs
                    | cons a as =>
                        cases as with
                        | nil => simp at hvs
                        | cons b bs =>
                            cases bs with
                            | nil => exact ⟨a, b, rfl⟩
                            | cons c cs => simp at hvs
                  subst hv
                  rw [hval]
                  have hstep : DriveState.step
                      ⟨toks, out, (ITag.tor, 1) :: ctrl', [x, y] ++ val', true⟩
                      = ⟨toks, out ++ [SLGate.orGate y x], ctrl', out.length :: val', true⟩ := by
                    simp [DriveState.step]
                  rw [hstep]
                  show PendingTop true ctrl' toks (out.length :: val')
                  cases hframes with
                  | nil => exact ⟨rfl, List.cons_ne_nil _ _⟩
                  | frame tag' ctrl'' ts' rest' vs' val'' harity' hdeep' =>
                      exact ⟨ts', rest', out.length :: vs', val'', by simp, by omega,
                        by simp at harity' ⊢; omega, rfl, by simp, hdeep'⟩

/-- The pending decomposition holds at **every** point of the run from the initial state. -/
theorem pending_iterate {n : Nat} (c : CircuitTree n) (k : Nat) :
    (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).Pending := by
  induction k with
  | zero => exact pending_init c
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact pending_step _ ih

/-- **Sink soundness.**  At any reachable state, if the driver is settling with an empty control stack
then the certificate is exhausted — the machine sink test never fires early. -/
theorem driver_sink_sound {n : Nat} (c : CircuitTree n) (k : Nat)
    (hset : (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).settling = true)
    (hctrl : (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).ctrl = []) :
    (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).toks = [] := by
  have hp := pending_iterate c k
  unfold DriveState.Pending at hp
  rw [hset, hctrl] at hp
  exact hp.1

/-- At the sink, the completed root's WORK index tops the value stack. -/
theorem driver_sink_val_ne_nil {n : Nat} (c : CircuitTree n) (k : Nat)
    (hset : (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).settling = true)
    (hctrl : (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).ctrl = []) :
    (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).val ≠ [] := by
  have hp := pending_iterate c k
  unfold DriveState.Pending at hp
  rw [hset, hctrl] at hp
  exact hp.2

/-- Every **below-top** control frame is bounded: `1 ≤ rem ≤ tag.arity` — so an on-tape frame is a
fixed-width (≤ 6-cell) object and the settle decrement is a bounded rewrite. -/
theorem pendingFrames_rem_bounds {n : Nat} {ctrl : List (ITag × Nat)} {rest : List (PreToken n)}
    {val : List Nat} (h : PendingFrames ctrl rest val) :
    ∀ f ∈ ctrl, 1 ≤ f.2 ∧ f.2 ≤ f.1.arity := by
  induction h with
  | nil => intro f hf; simp at hf
  | frame tag ctrl' ts rest' vs val' harity hdeep ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf'
      · exact ⟨by omega, by simp; omega⟩
      · exact ih f hf'

/-- A non-terminal reachable state stepping **into** a terminal state must be the settle-empty arm: it is
settling with an empty control stack and an exhausted certificate, and the step changes nothing but the
flag (in particular WORK is already final). -/
theorem pending_pre_terminal {n : Nat} (s : DriveState n) (hp : s.Pending)
    (hnt : ¬ s.terminal) (ht : s.step.terminal) :
    s.settling = true ∧ s.ctrl = [] ∧ s.toks = [] ∧ s.step.out = s.out := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := s
  replace hp : PendingTop settling ctrl toks val := hp
  cases settling with
  | false =>
      cases toks with
      | nil => exact absurd ⟨rfl, rfl⟩ hnt
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              have hstep : DriveState.step ⟨PreToken.leaf g :: toks', out, ctrl, val, false⟩
                  = ⟨toks', out ++ [g], ctrl, out.length :: val, true⟩ := by
                simp [DriveState.step]
              rw [hstep] at ht
              exact absurd ht.1 (by simp)
          | node tag =>
              have hstep : DriveState.step ⟨PreToken.node tag :: toks', out, ctrl, val, false⟩
                  = ⟨toks', out, (tag, tag.arity) :: ctrl, val, false⟩ := by
                simp [DriveState.step]
              rw [hstep] at ht
              exact absurd ht.2 (pending_reading_node hp)
  | true =>
      cases ctrl with
      | nil =>
          obtain ⟨htoks, -⟩ := hp
          exact ⟨rfl, rfl, htoks, rfl⟩
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          obtain ⟨ts, rest, vs, val', hrem, hpos, harity, htoks, hval, hframes⟩ := hp
          cases ts with
          | cons t₁ ts'' =>
              -- decrement arm: tokens unchanged and nonempty — the post-state is not terminal.
              have hne : rem ≠ 1 := by simp at hrem; omega
              have hstep : DriveState.step ⟨toks, out, (tag, rem) :: ctrl', val, true⟩
                  = ⟨toks, out, (tag, rem - 1) :: ctrl', val, false⟩ := by
                simp [DriveState.step, hne]
              rw [hstep] at ht
              refine absurd ht.2 ?_
              rw [htoks, preorderForest_cons, List.append_assoc]
              exact append_left_ne_nil (preorder_ne_nil t₁)
          | nil =>
              -- pop-emit arm: the post-state is settling — not terminal.
              have hrem1 : rem = 1 := by simpa using hrem
              subst hrem1
              cases tag with
              | tnot =>
                  have hvs : vs.length = 1 := by simpa [ITag.arity] using harity
                  obtain ⟨v, hv⟩ : ∃ v, vs = [v] := by
                    cases vs with
                    | nil => simp at hvs
                    | cons a as =>
                        cases as with
                        | nil => exact ⟨a, rfl⟩
                        | cons b bs => simp at hvs
                  subst hv
                  rw [hval] at ht
                  have hstep : DriveState.step ⟨toks, out, (ITag.tnot, 1) :: ctrl', [v] ++ val', true⟩
                      = ⟨toks, out ++ [SLGate.notGate v], ctrl', out.length :: val', true⟩ := by
                    simp [DriveState.step]
                  rw [hstep] at ht
                  exact absurd ht.1 (by simp)
              | tand =>
                  have hvs : vs.length = 2 := by simpa [ITag.arity] using harity
                  obtain ⟨x, y, hv⟩ : ∃ x y, vs = [x, y] := by
                    cases vs with
                    | nil => simp at hvs
                    | cons a as =>
                        cases as with
                        | nil => simp at hvs
                        | cons b bs =>
                            cases bs with
                            | nil => exact ⟨a, b, rfl⟩
                            | cons c cs => simp at hvs
                  subst hv
                  rw [hval] at ht
                  have hstep : DriveState.step
                      ⟨toks, out, (ITag.tand, 1) :: ctrl', [x, y] ++ val', true⟩
                      = ⟨toks, out ++ [SLGate.andGate y x], ctrl', out.length :: val', true⟩ := by
                    simp [DriveState.step]
                  rw [hstep] at ht
                  exact absurd ht.1 (by simp)
              | tor =>
                  have hvs : vs.length = 2 := by simpa [ITag.arity] using harity
                  obtain ⟨x, y, hv⟩ : ∃ x y, vs = [x, y] := by
                    cases vs with
                    | nil => simp at hvs
                    | cons a as =>
                        cases as with
                        | nil => simp at hvs
                        | cons b bs =>
                            cases bs with
                            | nil => exact ⟨a, b, rfl⟩
                            | cons c cs => simp at hvs
                  subst hv
                  rw [hval] at ht
                  have hstep : DriveState.step
                      ⟨toks, out, (ITag.tor, 1) :: ctrl', [x, y] ++ val', true⟩
                      = ⟨toks, out ++ [SLGate.orGate y x], ctrl', out.length :: val', true⟩ := by
                    simp [DriveState.step]
                  rw [hstep] at ht
                  exact absurd ht.1 (by simp)

/-- **The machine sink is reached — with the flatten already in WORK.**  Within `3 · c.size` micro-steps
the run hits a state that is settling with an empty control stack and an exhausted certificate, whose WORK
is exactly `(flatten c).gates`.  (The pure terminal state is entered only via the settle-empty arm, which
changes nothing but the flag — so the on-tape loop may halt at this sink without running that last step.) -/
theorem driver_sink_exists {n : Nat} (c : CircuitTree n) :
    ∃ k < 3 * c.size,
      (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).settling = true
      ∧ (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).ctrl = []
      ∧ (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).toks = []
      ∧ (DriveState.step^[k] (⟨preorder c, [], [], [], false⟩ : DriveState n)).out
          = (CircuitTree.flatten c).gates := by
  classical
  set s0 : DriveState n := ⟨preorder c, [], [], [], false⟩ with hs0
  have hbound := driveStep_halts_bound c
  have hex : ∃ k, (DriveState.step^[k] s0).terminal := ⟨3 * c.size, hbound.1⟩
  set K := Nat.find hex with hK
  have hKterm : (DriveState.step^[K] s0).terminal := Nat.find_spec hex
  have hKle : K ≤ 3 * c.size := Nat.find_le hbound.1
  have hK0 : K ≠ 0 := by
    intro h0
    have hterm0 : s0.terminal := by rw [h0] at hKterm; exact hKterm
    obtain ⟨-, htoks⟩ := hterm0
    have hnil : preorder c = [] := htoks
    have hlen := preorder_length c
    have hpos := CircuitTree.one_le_size c
    rw [hnil] at hlen
    simp at hlen
    omega
  have hpred : ¬ (DriveState.step^[K - 1] s0).terminal := Nat.find_min hex (by omega)
  have hKeq : K - 1 + 1 = K := by omega
  have hsucc : DriveState.step^[K] s0 = DriveState.step (DriveState.step^[K - 1] s0) := by
    conv_lhs => rw [← hKeq]
    rw [Function.iterate_succ_apply']
  have hstepterm : (DriveState.step (DriveState.step^[K - 1] s0)).terminal := by
    rw [← hsucc]; exact hKterm
  obtain ⟨hset, hctrl, htoks, hout⟩ :=
    pending_pre_terminal (DriveState.step^[K - 1] s0) (pending_iterate c (K - 1)) hpred hstepterm
  refine ⟨K - 1, by omega, hset, hctrl, htoks, ?_⟩
  -- WORK at the sink = WORK at the terminal state = the flatten (terminal states are absorbing).
  have habs : DriveState.step^[3 * c.size] s0 = DriveState.step^[K] s0 :=
    DriveState.step_after_terminal s0 hKterm hKle
  have hKout : (DriveState.step^[K] s0).out = (CircuitTree.flatten c).gates := by
    rw [← habs]; exact hbound.2
  rw [hsucc] at hKout
  rw [hout] at hKout
  exact hKout

end ContractExpansion
end Frontier
end Pnp4
