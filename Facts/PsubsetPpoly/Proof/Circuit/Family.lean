import Proof.Circuit.Tree
import Mathlib.Data.List.Basic

/-!
# Basic circuit combinators for the `P ⊆ P/poly` fact

This module provides the lightweight gate-counting infrastructure used to
analyse the gadgets in `Simulation.lean`.  The original development bundled a
richer counting theory; the standalone fact keeps only the helper definitions
that appear in the proof of `P ⊆ P/poly`.
-/

namespace Boolcube
namespace Circuit

/--
Simple gate count for the inductive circuit representation.  Unlike the derived
`sizeOf`, `gateCount` is designed to satisfy algebraic identities that make
bounds more pleasant to manipulate.
-/
def gateCount {n : ℕ} : Circuit n → ℕ
  | var _      => 1
  | const _    => 1
  | not c      => gateCount c + 1
  | and c₁ c₂  => gateCount c₁ + gateCount c₂ + 1
  | or  c₁ c₂  => gateCount c₁ + gateCount c₂ + 1

/-- An accumulator summing the gate counts of a list of circuits. -/
def listGateCount {n : ℕ} : List (Circuit n) → ℕ
  | []       => 0
  | c :: cs  => gateCount c + listGateCount cs

@[simp] lemma listGateCount_nil {n} :
    listGateCount ([] : List (Circuit n)) = 0 := rfl

@[simp] lemma listGateCount_cons {n} (c : Circuit n) (cs : List (Circuit n)) :
    listGateCount (c :: cs) = gateCount c + listGateCount cs := rfl

/--
The inductive `sizeOf` measure is always bounded by our explicit gate count.
This lemma lets us translate combinatorial bounds on `gateCount` into the
`sizeOf` inequalities demanded by the `InPpoly` interface.
-/
lemma sizeOf_le_gateCount {n : ℕ} : ∀ c : Circuit n, sizeOf c ≤ gateCount c := by
  intro c; induction c with
  | var i => simp [gateCount]
  | const b => simp [gateCount]
  | not c ih =>
      simpa [gateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.succ_le_succ ih
  | and c₁ c₂ ih₁ ih₂ =>
      have h := Nat.add_le_add ih₁ ih₂
      simpa [gateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.succ_le_succ h
  | or c₁ c₂ ih₁ ih₂ =>
      have h := Nat.add_le_add ih₁ ih₂
      simpa [gateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.succ_le_succ h

/--
Fold `bigOr` over a list of circuits by first building the tree and then
applying the semantics.  The helper satisfies the expected recursion and keeps
`bigOr` specialised to the circuit language.
-/
def bigOr {n : ℕ} : List (Circuit n) → Circuit n
  | []       => const false
  | c :: cs  => or c (bigOr cs)

@[simp] lemma bigOr_nil {n} : bigOr ([] : List (Circuit n)) = const false := rfl

@[simp] lemma bigOr_cons {n} (c : Circuit n) (cs : List (Circuit n)) :
    bigOr (c :: cs) = or c (bigOr cs) := rfl

@[simp] lemma eval_bigOr {n : ℕ} (cs : List (Circuit n)) (x : Point n) :
    eval (bigOr cs) x = (cs.map fun c => eval c x).foldr (fun b acc => b || acc) false := by
  induction cs with
  | nil => simp [bigOr]
  | cons c cs ih =>
      simp [bigOr, ih, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]

@[simp] lemma eval_bigOr_any {n : ℕ} (cs : List (Circuit n)) (x : Point n) :
    eval (bigOr cs) x = List.any cs (fun c => eval c x) := by
  induction cs with
  | nil => simp [bigOr]
  | cons c cs ih =>
      simp [bigOr, ih, Bool.or_left_comm, Bool.or_assoc]

/-- The gate count of a `bigOr` circuit sums the counts of its inputs. -/
lemma gateCount_bigOr {n} (cs : List (Circuit n)) :
    gateCount (bigOr cs) = listGateCount cs + 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simpa [bigOr, listGateCount_cons, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using ih

/--
Simple upper bound on the gate count of a folded OR.  Each recursive step
introduces one additional `or` gate and adds the gate count of the head.
-/
lemma gateCount_bigOr_le {n : ℕ} :
    ∀ cs : List (Circuit n), gateCount (bigOr cs) ≤ 1 + cs.length + listGateCount cs := by
  intro cs; induction cs with
  | nil => simp [bigOr, gateCount]
  | cons c cs ih =>
      have h := Nat.add_le_add_left (Nat.succ_le_succ ih) (gateCount c)
      have hlen : (c :: cs).length = cs.length + 1 := rfl
      have hsum : listGateCount (c :: cs) = gateCount c + listGateCount cs := rfl
      have := by
        simpa [bigOr, gateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using h
      simpa [hlen, hsum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this

end Circuit
end Boolcube
