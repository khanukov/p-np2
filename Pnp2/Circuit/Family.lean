import Pnp2.canonical_circuit
import Pnp2.Circuit.StraightLine
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic

/--
`Pnp2.Circuit.Family` collects a handful of convenience lemmas about the
minimal Boolean-circuit language used throughout the project.  The goal is
to encapsulate simple reasoning principles—gate counting and evaluation of
folded ORs—so that longer arguments (notably the proof that `P ⊆ P/poly`)
can reuse them without re-deriving the same inductions.
-/

namespace Boolcube
namespace Circuit

/--
Simple gate count for the inductive circuit representation.  Unlike the
derived `sizeOf`, `gateCount` is designed to satisfy elementary algebraic
identities that make bounds more pleasant to manipulate.
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

@[simp] lemma listGateCount_nil {n} : listGateCount ([] : List (Circuit n)) = 0 := rfl

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
Balanced OR of a list of circuits.  The base case is `false`, which keeps the
definition compatible with empty lists and simplifies algebraic bounds.
-/
def bigOr {n : ℕ} : List (Circuit n) → Circuit n
  | []       => const false
  | c :: cs  => or c (bigOr cs)

@[simp] lemma bigOr_nil {n} : bigOr ([] : List (Circuit n)) = const false := rfl

@[simp] lemma bigOr_cons {n} (c : Circuit n) (cs : List (Circuit n)) :
    bigOr (c :: cs) = or c (bigOr cs) := rfl

@[simp] lemma eval_bigOr {n : ℕ} (cs : List (Circuit n)) (x : Point n) :
    eval (bigOr cs) x = (cs.map (fun c => eval c x)).foldr (fun b acc => b || acc) false := by
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

/--
Simple upper bound on the gate count of a folded OR.  Each recursive step
introduces one additional `or` gate and adds the gate count of the head.
-/
lemma gateCount_bigOr_le {n : ℕ} :
    ∀ cs : List (Circuit n), gateCount (bigOr cs) ≤ 1 + cs.length + listGateCount cs := by
  intro cs; induction cs with
  | nil => simp [bigOr, gateCount]
  | cons c cs ih =>
      have h :=
        Nat.add_le_add_left (Nat.succ_le_succ ih) (gateCount c)
      have hlen : (c :: cs).length = cs.length + 1 := rfl
      have hsum : listGateCount (c :: cs) = gateCount c + listGateCount cs := rfl
      have := by
        simpa [bigOr, gateCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using h
      simpa [hlen, hsum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this

/-!
### Encoding circuits with bounded size

To bound the number of circuits of a given gate count we serialise every
circuit into a list of natural numbers.  The encoding is injective, its length
is `O(gateCount c)`, and all entries are bounded by a simple linear function of
`n` and `gateCount c`.  These facts allow us to embed the set of bounded-size
circuits into a finite product of `Fin`-types and derive explicit polynomial
counting bounds.
-/

/-- A compact prefix-style encoding of a Boolean circuit.  The first entry is a
tag identifying the constructor; for the composite constructors we record the
lengths of the recursively encoded children before appending their payloads. -/
def encodeData {n : ℕ} : Circuit n → List ℕ
  | var i      => [0, i]
  | const b    => [1, cond b 1 0]
  | not c      => 2 :: (encodeData c).length :: encodeData c
  | and c₁ c₂  =>
      3 :: (encodeData c₁).length :: (encodeData c₂).length ::
        (encodeData c₁ ++ encodeData c₂)
  | or c₁ c₂   =>
      4 :: (encodeData c₁).length :: (encodeData c₂).length ::
        (encodeData c₁ ++ encodeData c₂)

@[simp] lemma encodeData_var {n} (i : Fin n) :
    encodeData (Circuit.var i) = [0, i] := rfl

@[simp] lemma encodeData_const {n} (b : Bool) :
    encodeData (Circuit.const b) = [1, cond b 1 0] := rfl

@[simp] lemma encodeData_not {n} (c : Circuit n) :
    encodeData (Circuit.not c)
      = 2 :: (encodeData c).length :: encodeData c := rfl

@[simp] lemma encodeData_and {n} (c₁ c₂ : Circuit n) :
    encodeData (Circuit.and c₁ c₂)
      = 3 :: (encodeData c₁).length :: (encodeData c₂).length ::
          (encodeData c₁ ++ encodeData c₂) := rfl

@[simp] lemma encodeData_or {n} (c₁ c₂ : Circuit n) :
    encodeData (Circuit.or c₁ c₂)
      = 4 :: (encodeData c₁).length :: (encodeData c₂).length ::
          (encodeData c₁ ++ encodeData c₂) := rfl

/-- Injectivity of the raw encoding.  The proof proceeds by structural
induction, repeatedly peeling off the head elements of the two encodings and
using list operations (`take`, `drop`) to recover the recursively encoded
subcircuits. -/
lemma encodeData_injective {n : ℕ} :
    Function.Injective (encodeData (n := n)) := by
  intro c₁ c₂ henc; induction c₁ generalizing c₂ with
  | var i =>
      cases c₂ with
      | var j => simpa using henc
      | const b => simpa using henc
      | not c => simpa using henc
      | and c₁ c₂ => simpa using henc
      | or c₁ c₂ => simpa using henc
  | const b =>
      cases c₂ with
      | var i => simpa using henc
      | const b' => simpa using henc
      | not c => simpa using henc
      | and c₁ c₂ => simpa using henc
      | or c₁ c₂ => simpa using henc
  | not c ih =>
      cases c₂ with
      | var i => simpa using henc
      | const b => simpa using henc
      | not d =>
          have h := (List.cons_eq_cons.mp henc).2
          have hlen := (List.cons_eq_cons.mp h).1
          have hrest := (List.cons_eq_cons.mp h).2
          have hsub := List.cons_eq_cons.mp hrest
          have hpayload := (List.cons_eq_cons.mp hrest).2
          have hencSub := hpayload
          have hchild := ih hencSub
          exact congrArg Circuit.not hchild
      | and c₁ c₂ => simpa using henc
      | or c₁ c₂ => simpa using henc
  | and c₁ c₂ ih₁ ih₂ =>
      cases c₂ with
      | var i => simpa using henc
      | const b => simpa using henc
      | not d => simpa using henc
      | and d₁ d₂ =>
          -- Decompose the equality into length and payload components.
          have h := List.cons_eq_cons.mp henc
          have htail := List.cons_eq_cons.mp h.2
          have hlen₁ := List.cons_eq_cons.mp htail
          have hlen₂ := List.cons_eq_cons.mp hlen₁.2
          have hpayload := hlen₂.2
          have hlen₁' : (encodeData c₁).length = (encodeData d₁).length := hlen₁.1
          have hlen₂' : (encodeData c₂).length = (encodeData d₂).length := hlen₂.1
          -- Extract the first child via `take`.
          have hchild₁ := congrArg (List.take (encodeData c₁).length) hpayload
          have hchild₂ := congrArg (List.drop (encodeData c₁).length) hpayload
          have henc₁ : encodeData c₁ = encodeData d₁ := by
            simpa [List.take_append_of_le_length, hlen₁', List.take_length]
              using hchild₁
          have henc₂ : encodeData c₂ = encodeData d₂ := by
            have hdrop₁ :
                List.drop (encodeData c₁).length (encodeData c₁ ++ encodeData c₂)
                  = encodeData c₂ := by
              simpa [List.drop_append, List.drop_length] using rfl
            have hdrop₂ :
                List.drop (encodeData c₁).length (encodeData d₁ ++ encodeData d₂)
                  = encodeData d₂ := by
              simpa [List.drop_append, List.drop_length, hlen₁'] using rfl
            simpa [hdrop₁, hdrop₂] using hchild₂
          have hc₁ := ih₁ henc₁
          have hc₂ := ih₂ henc₂
          exact congrArg₂ Circuit.and hc₁ hc₂
      | or d₁ d₂ => simpa using henc
  | or c₁ c₂ ih₁ ih₂ =>
      cases c₂ with
      | var i => simpa using henc
      | const b => simpa using henc
      | not d => simpa using henc
      | and d₁ d₂ => simpa using henc
      | or d₁ d₂ =>
          have h := List.cons_eq_cons.mp henc
          have htail := List.cons_eq_cons.mp h.2
          have hlen₁ := List.cons_eq_cons.mp htail
          have hlen₂ := List.cons_eq_cons.mp hlen₁.2
          have hpayload := hlen₂.2
          have hlen₁' : (encodeData c₁).length = (encodeData d₁).length := hlen₁.1
          have hlen₂' : (encodeData c₂).length = (encodeData d₂).length := hlen₂.1
          have hchild₁ := congrArg (List.take (encodeData c₁).length) hpayload
          have hchild₂ := congrArg (List.drop (encodeData c₁).length) hpayload
          have henc₁ : encodeData c₁ = encodeData d₁ := by
            simpa [List.take_append_of_le_length, hlen₁', List.take_length]
              using hchild₁
          have henc₂ : encodeData c₂ = encodeData d₂ := by
            have hdrop₁ :
                List.drop (encodeData c₁).length (encodeData c₁ ++ encodeData c₂)
                  = encodeData c₂ := by
              simpa [List.drop_append, List.drop_length] using rfl
            have hdrop₂ :
                List.drop (encodeData c₁).length (encodeData d₁ ++ encodeData d₂)
                  = encodeData d₂ := by
              simpa [List.drop_append, List.drop_length, hlen₁'] using rfl
            simpa [hdrop₁, hdrop₂] using hchild₂
          have hc₁ := ih₁ henc₁
          have hc₂ := ih₂ henc₂
          exact congrArg₂ Circuit.or hc₁ hc₂

/-- The encoding has length at most `4 * gateCount c`.  Each recursive step
adds a constant number of tokens (for the tag and the length fields) in
addition to the payload of the subcircuits. -/
lemma encodeData_length_le {n : ℕ} :
    ∀ c : Circuit n, (encodeData c).length ≤ 4 * gateCount c := by
  intro c; induction c with
  | var i => simp [encodeData, gateCount]
  | const b => simp [encodeData, gateCount]
  | not c ih =>
      have := ih
      have := Nat.succ_le_succ this
      simpa [encodeData, gateCount, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | and c₁ c₂ ih₁ ih₂ =>
      have h₁ := ih₁
      have h₂ := ih₂
      have := Nat.succ_le_succ (Nat.succ_le_succ (Nat.add_le_add h₁ h₂))
      simpa [encodeData, gateCount, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | or c₁ c₂ ih₁ ih₂ =>
      have h₁ := ih₁
      have h₂ := ih₂
      have := Nat.succ_le_succ (Nat.succ_le_succ (Nat.add_le_add h₁ h₂))
      simpa [encodeData, gateCount, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Each token in the encoding is bounded by `max n (4 * gateCount c) + 4`.
The bound is generous but sufficient for the counting arguments below. -/
lemma encodeData_entry_le {n : ℕ} :
    ∀ c : Circuit n, ∀ x ∈ encodeData c,
      x ≤ Nat.max n (4 * gateCount c) + 4 := by
  intro c; induction c with
  | var i =>
      intro x hx
      have hx' : x = 0 ∨ x = (i : ℕ) := by
        simpa [encodeData] using hx
      rcases hx' with rfl | rfl
      · have := Nat.le_max_right n (4 * gateCount (Circuit.var i))
        simpa [gateCount] using add_le_add_right this 4
      · have hi : (i : ℕ) < n := i.is_lt
        have := Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)
        have := Nat.succ_le_of_lt this
        simpa [gateCount] using this
  | const b =>
      intro x hx
      have hx' : x = 1 ∨ x = cond b 1 0 := by
        simpa [encodeData] using hx
      rcases hx' with rfl | rfl
      · have := Nat.le_max_right n (4 * gateCount (Circuit.const b))
        simpa [gateCount] using add_le_add_right this 4
      · cases b <;> simp [encodeData, gateCount]
  | not c ih =>
      intro x hx
      have hx' : x = 2 ∨ x = (encodeData c).length ∨ x ∈ encodeData c := by
        simpa [encodeData, or_left_comm, or_assoc] using hx
      rcases hx' with rfl | hx'
      · have := Nat.le_max_right n (4 * gateCount (Circuit.not c))
        simpa [gateCount] using add_le_add_right this 4
      · rcases hx' with rfl | hx''
        · have hlen := encodeData_length_le (n := n) (c := c)
          have hgate : gateCount c ≤ gateCount (Circuit.not c) := by
            simp [gateCount]
          have := le_trans hlen (Nat.mul_le_mul_left _ hgate)
          have := Nat.max_le_max (le_rfl : n ≤ n) this
          simpa [gateCount] using add_le_add_right this 4
        · have := ih _ hx''
          have hgate : gateCount c ≤ gateCount (Circuit.not c) := by
            simp [gateCount]
          have := Nat.max_le_max (le_rfl : n ≤ n) (Nat.mul_le_mul_left _ hgate)
          exact le_trans this (by simpa [gateCount] using add_le_add_right this 4)
  | and c₁ c₂ ih₁ ih₂ =>
      intro x hx
      have hx' : x = 3 ∨ x = (encodeData c₁).length ∨ x = (encodeData c₂).length
          ∨ x ∈ encodeData c₁ ∨ x ∈ encodeData c₂ := by
        simpa [encodeData, or_left_comm, or_assoc, and_or_left] using hx
      rcases hx' with rfl | hx'
      · have := Nat.le_max_right n (4 * gateCount (Circuit.and c₁ c₂))
        simpa [gateCount] using add_le_add_right this 4
      · rcases hx' with rfl | hx''
        · have hlen := encodeData_length_le (n := n) (c := c₁)
          have hgate : gateCount c₁ ≤ gateCount (Circuit.and c₁ c₂) := by
            simp [gateCount]
          have := le_trans hlen (Nat.mul_le_mul_left _ hgate)
          have := Nat.max_le_max (le_rfl : n ≤ n) this
          simpa [gateCount] using add_le_add_right this 4
        · rcases hx'' with rfl | hx'''
          · have hlen := encodeData_length_le (n := n) (c := c₂)
            have hgate : gateCount c₂ ≤ gateCount (Circuit.and c₁ c₂) := by
              simp [gateCount]
            have := le_trans hlen (Nat.mul_le_mul_left _ hgate)
            have := Nat.max_le_max (le_rfl : n ≤ n) this
            simpa [gateCount] using add_le_add_right this 4
          · rcases hx''' with hx₁ | hx₂
            · have := ih₁ _ hx₁
              have hgate : gateCount c₁ ≤ gateCount (Circuit.and c₁ c₂) := by
                simp [gateCount]
              have := Nat.max_le_max (le_rfl : n ≤ n) (Nat.mul_le_mul_left _ hgate)
              exact le_trans this (by simpa [gateCount] using add_le_add_right this 4)
            · have := ih₂ _ hx₂
              have hgate : gateCount c₂ ≤ gateCount (Circuit.and c₁ c₂) := by
                simp [gateCount]
              have := Nat.max_le_max (le_rfl : n ≤ n) (Nat.mul_le_mul_left _ hgate)
              exact le_trans this (by simpa [gateCount] using add_le_add_right this 4)
  | or c₁ c₂ ih₁ ih₂ =>
      intro x hx
      have hx' : x = 4 ∨ x = (encodeData c₁).length ∨ x = (encodeData c₂).length
          ∨ x ∈ encodeData c₁ ∨ x ∈ encodeData c₂ := by
        simpa [encodeData, or_left_comm, or_assoc, and_or_left] using hx
      rcases hx' with rfl | hx'
      · have := Nat.le_max_right n (4 * gateCount (Circuit.or c₁ c₂))
        simpa [gateCount] using add_le_add_right this 4
      · rcases hx' with rfl | hx''
        · have hlen := encodeData_length_le (n := n) (c := c₁)
          have hgate : gateCount c₁ ≤ gateCount (Circuit.or c₁ c₂) := by
            simp [gateCount]
          have := le_trans hlen (Nat.mul_le_mul_left _ hgate)
          have := Nat.max_le_max (le_rfl : n ≤ n) this
          simpa [gateCount] using add_le_add_right this 4
        · rcases hx'' with rfl | hx'''
          · have hlen := encodeData_length_le (n := n) (c := c₂)
            have hgate : gateCount c₂ ≤ gateCount (Circuit.or c₁ c₂) := by
              simp [gateCount]
            have := le_trans hlen (Nat.mul_le_mul_left _ hgate)
            have := Nat.max_le_max (le_rfl : n ≤ n) this
            simpa [gateCount] using add_le_add_right this 4
          · rcases hx''' with hx₁ | hx₂
            · have := ih₁ _ hx₁
              have hgate : gateCount c₁ ≤ gateCount (Circuit.or c₁ c₂) := by
                simp [gateCount]
              have := Nat.max_le_max (le_rfl : n ≤ n) (Nat.mul_le_mul_left _ hgate)
              exact le_trans this (by simpa [gateCount] using add_le_add_right this 4)
            · have := ih₂ _ hx₂
              have hgate : gateCount c₂ ≤ gateCount (Circuit.or c₁ c₂) := by
                simp [gateCount]
              have := Nat.max_le_max (le_rfl : n ≤ n) (Nat.mul_le_mul_left _ hgate)
              exact le_trans this (by simpa [gateCount] using add_le_add_right this 4)

/-- Convert a list of natural numbers bounded by `A` into a list of elements of
`Fin (A + 1)`.  The function is defined by recursion and preserves the order of
the input list. -/
def listToFin {A : ℕ} :
    (xs : List ℕ) → (∀ x ∈ xs, x ≤ A) → List (Fin (A + 1))
  | [], _ => []
  | x :: xs, hx =>
      have hhead : x ≤ A := hx _ (by simp)
      have htail : ∀ y ∈ xs, y ≤ A := by
        intro y hy; exact hx _ (by simp [hy])
      ⟨x, Nat.lt_succ_of_le hhead⟩ :: listToFin xs htail

@[simp] lemma listToFin_length {A : ℕ} (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ A) :
    (listToFin xs h).length = xs.length := by
  induction xs generalizing h with
  | nil => simp [listToFin]
  | cons x xs ih =>
      simp [listToFin, ih]

@[simp] lemma listToFin_val {A : ℕ} (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ A) :
    (listToFin xs h).map (fun z => (z : ℕ)) = xs := by
  induction xs generalizing h with
  | nil => simp [listToFin]
  | cons x xs ih =>
      simp [listToFin, ih, List.map_cons, List.map]

/-- Pad a list with a default element to reach a prescribed length and package
the result as a vector. -/
def padWith {α : Type _} (xs : List α) (default : α) (L : ℕ)
    (h : xs.length ≤ L) : Vector α L :=
  ⟨xs ++ List.replicate (L - xs.length) default, by
      have hsum := Nat.add_sub_of_le h
      simpa [List.length_append, List.length_replicate, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, hsum]⟩

/-- Encode a circuit with gate count at most `m` as a fixed-length vector of
bounded natural numbers together with the length of the unpadded payload. -/
def encodeVector {n m : ℕ} (c : Circuit n) (h : gateCount c ≤ m) :
    Fin (4 * m + 1) × Vector (Fin (Nat.max n (4 * m) + 5)) (4 * m) := by
  classical
  set raw := encodeData (n := n) c
  have hlen : raw.length ≤ 4 * m := by
    have hlen₀ := encodeData_length_le (n := n) (c := c)
    have hmul : 4 * gateCount c ≤ 4 * m := Nat.mul_le_mul_left _ h
    exact hlen₀.trans hmul
  have hentries : ∀ x ∈ raw, x ≤ Nat.max n (4 * m) + 4 := by
    intro x hx
    have hx₀ := encodeData_entry_le (n := n) (c := c) x hx
    have hmul : 4 * gateCount c ≤ 4 * m := Nat.mul_le_mul_left _ h
    have hmax := Nat.max_le_max (le_rfl : n ≤ n) hmul
    exact hx₀.trans (add_le_add_right hmax 4)
  -- Convert the payload to a list of `Fin` values.
  let finList := listToFin (xs := raw) (A := Nat.max n (4 * m) + 4) hentries
  have hfin_len : finList.length = raw.length :=
    listToFin_length (xs := raw) (h := hentries)
  -- Package the data as a vector.
  refine ⟨⟨raw.length, ?_⟩, padWith finList 0 (4 * m) ?_⟩
  · have := Nat.lt_succ_of_le hlen
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  · simpa [hfin_len]

/-- Decoding the padded representation of a circuit recovers the original raw
encoding. -/
lemma decode_encodeVector {n m : ℕ} (c : Circuit n) (h : gateCount c ≤ m) :
    let enc := encodeVector (n := n) (m := m) c h
    ((enc.snd.toList.take enc.fst.val).map (fun z => (z : ℕ)))
      = encodeData (n := n) c := by
  classical
  dsimp [encodeVector]
  set raw := encodeData (n := n) c
  have hentries : ∀ x ∈ raw, x ≤ Nat.max n (4 * m) + 4 := by
    intro x hx
    have hx₀ := encodeData_entry_le (n := n) (c := c) x hx
    have hmul : 4 * gateCount c ≤ 4 * m := Nat.mul_le_mul_left _ h
    have hmax := Nat.max_le_max (le_rfl : n ≤ n) hmul
    exact hx₀.trans (add_le_add_right hmax 4)
  simp [padWith, listToFin_val (xs := raw) (h := hentries),
    List.take_append_of_le_length, List.take_length, Nat.min_eq_left] 

/-- The padded encoding is injective for circuits whose gate counts are bounded
by `m`. -/
lemma encodeVector_injective {n m : ℕ} :
    Function.Injective (fun c : {c : Circuit n // gateCount c ≤ m} =>
      encodeVector (n := n) (m := m) c c.property) := by
  intro c₁ c₂ henc
  have hdecode₁ := decode_encodeVector (n := n) (m := m) c₁.val c₁.property
  have hdecode₂ := decode_encodeVector (n := n) (m := m) c₂.val c₂.property
  have hraw : encodeData (n := n) c₁.val = encodeData (n := n) c₂.val := by
    simpa [hdecode₁, hdecode₂]
      using congrArg (fun p =>
        ((p.snd.toList.take p.fst.val).map fun z => (z : ℕ))) henc
  have := encodeData_injective (n := n) hraw
  exact Subtype.ext (by simpa using this)

end Circuit
end Boolcube

