import Complexity.Uniform.V1.Machine
import Mathlib.Data.List.OfFn

/-!
# Uniquely-decodable pairs for Uniform V1

The input is encoded as tagged data pairs, followed by one true separator and
the witness.  The complete finite word is uniquely decodable.  The family is
NOT globally prefix-free because extending a witness extends its encoding.
-/

namespace Pnp3.Complexity.Uniform.V1.PairEncoding

/-- Insert a false tag immediately before every input bit. -/
def tagList : List Bool → List Bool
  | [] => []
  | b :: rest => false :: b :: tagList rest

/-- Encode an input/witness pair as tagged input, separator, then witness. -/
def encodePairList (xs ws : List Bool) : List Bool :=
  tagList xs ++ true :: ws

/-- Structurally decode one complete finite pair word. -/
def decodePairList : List Bool → Option (List Bool × List Bool)
  | [] => none
  | true :: rest => some ([], rest)
  | [false] => none
  | false :: b :: rest =>
      match decodePairList rest with
      | none => none
      | some (xs, ws) => some (b :: xs, ws)

theorem tagList_length (xs : List Bool) :
    (tagList xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [tagList, ih, Nat.mul_add]

theorem encodePairList_length (xs ws : List Bool) :
    (encodePairList xs ws).length = 2 * xs.length + 1 + ws.length := by
  simp [encodePairList, tagList_length]
  omega

theorem tagList_tag (xs : List Bool) (i : Fin xs.length) :
    (tagList xs).get ⟨2 * i.val, by rw [tagList_length]; omega⟩ = false := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons b xs ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [tagList, Nat.mul_add, Nat.add_assoc] using ih j

theorem tagList_data (xs : List Bool) (i : Fin xs.length) :
    (tagList xs).get ⟨2 * i.val + 1, by simp [tagList_length]; omega⟩ = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons b xs ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa [tagList, Nat.mul_add, Nat.add_assoc] using ih j

theorem encodePairList_tag (xs ws : List Bool) (i : Fin xs.length) :
    (encodePairList xs ws).get
      ⟨2 * i.val, by simp [encodePairList_length]; omega⟩ = false := by
  unfold encodePairList
  rw [List.get_eq_getElem, List.getElem_append_left]
  simpa [List.get_eq_getElem] using tagList_tag xs i

theorem encodePairList_data (xs ws : List Bool) (i : Fin xs.length) :
    (encodePairList xs ws).get
      ⟨2 * i.val + 1, by simp [encodePairList_length]; omega⟩ = xs.get i := by
  unfold encodePairList
  rw [List.get_eq_getElem, List.getElem_append_left]
  simpa [List.get_eq_getElem] using tagList_data xs i

theorem encodePairList_separator (xs ws : List Bool) :
    (encodePairList xs ws).get
      ⟨2 * xs.length, by rw [encodePairList_length]; omega⟩ = true := by
  simp [encodePairList, tagList_length]

theorem encodePairList_witness (xs ws : List Bool) (j : Fin ws.length) :
    (encodePairList xs ws).get
      ⟨2 * xs.length + 1 + j.val, by rw [encodePairList_length]; omega⟩ = ws.get j := by
  unfold encodePairList
  rw [List.get_eq_getElem]
  change (tagList xs ++ true :: ws)[2 * xs.length + 1 + j.val]'(by
    simp [tagList_length]
    omega) = ws[j.val]
  rw [List.getElem_append_right (h₁ := by rw [tagList_length]; omega)]
  have hindex : 2 * xs.length + 1 + j.val - (tagList xs).length = j.val + 1 := by
    rw [tagList_length]
    omega
  simp [hindex]

theorem encodePairList_boundary (xs ws : List Bool) :
    (encodePairList xs ws).take (2 * xs.length) = tagList xs ∧
    (encodePairList xs ws).drop (2 * xs.length) = true :: ws := by
  simp [encodePairList, tagList_length]

/-- Extending the witness appends exactly the same suffix to the encoding.
This equality is a concrete prefix witness; the family is NOT globally
prefix-free. -/
theorem encodePairList_witness_extension_prefix (xs ws extra : List Bool) :
    encodePairList xs (ws ++ extra) = encodePairList xs ws ++ extra := by
  simp [encodePairList, List.append_assoc]

theorem decodePairList_roundtrip (xs ws : List Bool) :
    decodePairList (encodePairList xs ws) = some (xs, ws) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (match decodePairList (encodePairList xs ws) with
        | none => none
        | some (ys, zs) => some (b :: ys, zs)) = some (b :: xs, ws)
      rw [ih]

private theorem decodePairList_sound {l xs ws : List Bool}
    (h : decodePairList l = some (xs, ws)) : l = encodePairList xs ws := by
  cases l with
  | nil => simp [decodePairList] at h
  | cons a rest =>
      cases a with
      | true =>
          simp [decodePairList] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
      | false =>
          cases rest with
          | nil => simp [decodePairList] at h
          | cons b tail =>
              cases hd : decodePairList tail with
              | none => simp [decodePairList, hd] at h
              | some p =>
                  rcases p with ⟨ys, zs⟩
                  have ht := decodePairList_sound hd
                  simp [decodePairList, hd] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simp [encodePairList, tagList, ht]
termination_by l.length

theorem decodePairList_eq_some_iff (l xs ws : List Bool) :
    decodePairList l = some (xs, ws) ↔ l = encodePairList xs ws := by
  constructor
  · exact decodePairList_sound
  · rintro rfl
    exact decodePairList_roundtrip xs ws

theorem decodePairList_eq_none_iff (l : List Bool) :
    decodePairList l = none ↔ ¬ ∃ xs ws, l = encodePairList xs ws := by
  constructor
  · intro hnone
    rintro ⟨xs, ws, rfl⟩
    rw [decodePairList_roundtrip] at hnone
    contradiction
  · intro hno
    cases hdecode : decodePairList l with
    | none => rfl
    | some p =>
        rcases p with ⟨xs, ws⟩
        exact (hno ⟨xs, ws, decodePairList_sound hdecode⟩).elim

theorem encodePairList_injective :
    Function.Injective (Function.uncurry encodePairList) := by
  rintro ⟨xs, ws⟩ ⟨ys, zs⟩ h
  change encodePairList xs ws = encodePairList ys zs at h
  have := congrArg decodePairList h
  rw [decodePairList_roundtrip, decodePairList_roundtrip] at this
  have hp : (xs, ws) = (ys, zs) := Option.some.inj this
  exact hp

theorem decodePairList_tagList_none (xs : List Bool) :
    decodePairList (tagList xs) = none := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [tagList, decodePairList, ih]

theorem decodePairList_dangling_false_none (xs : List Bool) :
    decodePairList (tagList xs ++ [false]) = none := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [tagList, decodePairList, ih]

theorem decodePairList_nil : decodePairList [] = none := rfl
theorem decodePairList_false : decodePairList [false] = none := rfl
theorem decodePairList_false_true : decodePairList [false, true] = none := rfl
theorem decodePairList_true : decodePairList [true] = some ([], []) := rfl
theorem decodePairList_true_false :
    decodePairList [true, false] = some ([], [false]) := rfl

theorem encodePairList_two_one :
    encodePairList [true, false] [true] = [false, true, false, false, true, true] := rfl

theorem decodePairList_two_one :
    decodePairList [false, true, false, false, true, true] =
      some ([true, false], [true]) := rfl

/-- Exact length of an indexed pair word. -/
def pairLength (n m : Nat) : Nat := 2 * n + 1 + m

/-- A decoded pair retains both lengths and both indexed words. -/
abbrev DecodedPair := (Σ n, Bitstring n) × (Σ m, Bitstring m)

/-- A bitstring packaged with its length. -/
abbrev EncodedWord := Σ N, Bitstring N

theorem pairLength_eq (n m : Nat) : pairLength n m = 2 * n + 1 + m := rfl

/-- Direct indexed view of the exact finite list layout. -/
def encodePair {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    Bitstring (pairLength n m) := fun k =>
  (encodePairList (List.ofFn x) (List.ofFn w)).get
    ⟨k.val, by simpa only [encodePairList_length, List.length_ofFn, pairLength] using k.isLt⟩

theorem encodePair_tag {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Fin n) :
    encodePair x w ⟨2 * i.val, by simp [pairLength]; omega⟩ = false := by
  let i' : Fin (List.ofFn x).length := ⟨i.val, by rw [List.length_ofFn]; exact i.isLt⟩
  simpa [encodePair, i'] using encodePairList_tag (List.ofFn x) (List.ofFn w) i'

theorem encodePair_data {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Fin n) :
    encodePair x w ⟨2 * i.val + 1, by simp [pairLength]; omega⟩ = x i := by
  let i' : Fin (List.ofFn x).length := ⟨i.val, by rw [List.length_ofFn]; exact i.isLt⟩
  simpa [encodePair, List.get_ofFn, i'] using
    encodePairList_data (List.ofFn x) (List.ofFn w) i'

theorem encodePair_separator {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    encodePair x w ⟨2 * n, by rw [pairLength_eq]; omega⟩ = true := by
  simpa [encodePair] using encodePairList_separator (List.ofFn x) (List.ofFn w)

theorem encodePair_witness {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin m) :
    encodePair x w ⟨2 * n + 1 + j.val, by rw [pairLength_eq]; omega⟩ = w j := by
  let j' : Fin (List.ofFn w).length := ⟨j.val, by rw [List.length_ofFn]; exact j.isLt⟩
  simpa [encodePair, List.get_ofFn, j'] using
    encodePairList_witness (List.ofFn x) (List.ofFn w) j'

theorem encodePair_boundary {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ i : Fin n,
      encodePair x w ⟨2 * i.val, by simp [pairLength]; omega⟩ = false) ∧
    encodePair x w ⟨2 * n, by simp [pairLength]; omega⟩ = true := by
  exact ⟨encodePair_tag x w, encodePair_separator x w⟩

theorem encodePair_toList {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    List.ofFn (encodePair x w) = encodePairList (List.ofFn x) (List.ofFn w) := by
  apply List.ext_get
  · simp [encodePairList_length, pairLength]
  · intro k hk₁ hk₂
    simp [encodePair]

/-- Decode through the list grammar and reindex the recovered finite lists. -/
def decodePair {N : Nat} (y : Bitstring N) : Option DecodedPair :=
  match decodePairList (List.ofFn y) with
  | none => none
  | some (xs, ws) => some (⟨xs.length, xs.get⟩, ⟨ws.length, ws.get⟩)

theorem decodePair_roundtrip {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    decodePair (encodePair x w) =
      some ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) := by
  rw [decodePair, encodePair_toList, decodePairList_roundtrip]
  have hx := List.equivSigmaTuple.right_inv (⟨n, x⟩ : Σ k, Fin k → Bool)
  have hw := List.equivSigmaTuple.right_inv (⟨m, w⟩ : Σ k, Fin k → Bool)
  exact congrArg some (congrArg₂ Prod.mk hx hw)

/-- Exact packed image of the dependent decoder, preserving both recovered
lengths and both indexed words. -/
theorem decodePair_eq_some_iff {N : Nat} (y : Bitstring N)
    (p : DecodedPair) :
    decodePair y = some p ↔
      (⟨N, y⟩ : EncodedWord) =
        (⟨pairLength p.1.1 p.2.1,
          encodePair p.1.2 p.2.2⟩ : EncodedWord) := by
  rcases p with ⟨⟨n, x⟩, ⟨m, w⟩⟩
  constructor
  · intro h
    cases hd : decodePairList (List.ofFn y) with
    | none =>
        simp [decodePair, hd] at h
    | some q =>
        rcases q with ⟨xs, ws⟩
        have hp :
            ((⟨xs.length, xs.get⟩, ⟨ws.length, ws.get⟩) :
                DecodedPair) =
              ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) := by
          simpa only [decodePair, hd, Option.some.injEq] using h
        have hl : List.ofFn y = encodePairList xs ws :=
          (decodePairList_eq_some_iff (List.ofFn y) xs ws).1 hd
        have hxs : List.ofFn xs.get = xs :=
          List.equivSigmaTuple.left_inv xs
        have hws : List.ofFn ws.get = ws :=
          List.equivSigmaTuple.left_inv ws
        have hword :
            (⟨N, y⟩ : EncodedWord) =
              (⟨pairLength xs.length ws.length,
                encodePair xs.get ws.get⟩ : EncodedWord) := by
          apply (List.equivSigmaTuple :
            List Bool ≃ EncodedWord).symm.injective
          change List.ofFn y = List.ofFn (encodePair xs.get ws.get)
          rw [encodePair_toList, hxs, hws]
          exact hl
        have hpack :
            (⟨pairLength xs.length ws.length,
              encodePair xs.get ws.get⟩ : EncodedWord) =
              (⟨pairLength n m, encodePair x w⟩ : EncodedWord) :=
          congrArg
            (fun q : DecodedPair =>
              (⟨pairLength q.1.1 q.2.1,
                encodePair q.1.2 q.2.2⟩ : EncodedWord))
            hp
        exact hword.trans hpack
  · intro h
    have hd := congrArg (fun z : EncodedWord => decodePair z.2) h
    simpa only [decodePair_roundtrip] using hd

/-- Failure of the dependent decoder is exactly nonmembership in the packed
image of `encodePair`. -/
theorem decodePair_eq_none_iff {N : Nat} (y : Bitstring N) :
    decodePair y = none ↔
      ¬ ∃ p : DecodedPair,
        (⟨N, y⟩ : EncodedWord) =
          (⟨pairLength p.1.1 p.2.1,
            encodePair p.1.2 p.2.2⟩ : EncodedWord) := by
  constructor
  · intro hn hex
    rcases hex with ⟨p, hp⟩
    have hs : decodePair y = some p :=
      (decodePair_eq_some_iff y p).2 hp
    rw [hn] at hs
    contradiction
  · intro hno
    cases hd : decodePair y with
    | none => rfl
    | some p =>
        exact
          (hno ⟨p, (decodePair_eq_some_iff y p).1 hd⟩).elim

theorem encodePair_packed_injective :
    Function.Injective
      (fun p : DecodedPair =>
        (⟨pairLength p.1.1 p.2.1, encodePair p.1.2 p.2.2⟩ : EncodedWord)) := by
  intro p q h
  have hd := congrArg (fun z : EncodedWord => decodePair z.2) h
  simp only [decodePair_roundtrip, Option.some.injEq] at hd
  exact hd

theorem encodePair_injective {n m : Nat} :
    Function.Injective
      (fun p : Bitstring n × Bitstring m => encodePair p.1 p.2) := by
  rintro ⟨x, w⟩ ⟨y, z⟩ h
  have hd := congrArg decodePair h
  simp only [decodePair_roundtrip, Option.some.injEq] at hd
  cases hd
  rfl

theorem initialConfig_pair_tag (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) (i : Fin n) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * i.val, by simp [tapeLength, pairLength]; omega⟩ = some false := by
  let k : Fin (pairLength n m) :=
    ⟨2 * i.val, by rw [pairLength_eq]; omega⟩
  have ht :=
    initialConfig_tape_input (budget := budget) M (encodePair x w) k
  have hk : encodePair x w k = false := by
    simpa [k] using encodePair_tag x w i
  simpa [k, hk] using ht

theorem initialConfig_pair_data (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) (i : Fin n) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * i.val + 1, by simp [tapeLength, pairLength]; omega⟩ = some (x i) := by
  let k : Fin (pairLength n m) :=
    ⟨2 * i.val + 1, by rw [pairLength_eq]; omega⟩
  have ht :=
    initialConfig_tape_input (budget := budget) M (encodePair x w) k
  have hk : encodePair x w k = x i := by
    simpa [k] using encodePair_data x w i
  simpa [k, hk] using ht

theorem initialConfig_pair_separator (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * n, by simp [tapeLength, pairLength]; omega⟩ = some true := by
  let k : Fin (pairLength n m) :=
    ⟨2 * n, by rw [pairLength_eq]; omega⟩
  have ht :=
    initialConfig_tape_input (budget := budget) M (encodePair x w) k
  have hk : encodePair x w k = true := by
    simpa [k] using encodePair_separator x w
  simpa [k, hk] using ht

theorem initialConfig_pair_witness (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m) (j : Fin m) :
    (initialConfig M budget (encodePair x w)).tape
      ⟨2 * n + 1 + j.val, by simp [tapeLength, pairLength]; omega⟩ = some (w j) := by
  let k : Fin (pairLength n m) :=
    ⟨2 * n + 1 + j.val, by rw [pairLength_eq]; omega⟩
  have ht :=
    initialConfig_tape_input (budget := budget) M (encodePair x w) k
  have hk : encodePair x w k = w j := by
    simpa [k] using encodePair_witness x w j
  simpa [k, hk] using ht

theorem initialConfig_pair_padding (M : UniformTM) {n m budget : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) budget)) (h : pairLength n m ≤ i.val) :
    (initialConfig M budget (encodePair x w)).tape i = none :=
  initialConfig_tape_padding M (encodePair x w) i h

theorem decodePair_empty :
    let x : Bitstring 0 := fun i => Fin.elim0 i
    let w : Bitstring 0 := fun i => Fin.elim0 i
    decodePair (encodePair x w) =
      some ((⟨0, x⟩, ⟨0, w⟩) : DecodedPair) := by
  exact decodePair_roundtrip _ _

theorem decodePair_two_one :
    let x : Bitstring 2 := fun i => decide (i.val = 0)
    let w : Bitstring 1 := fun _ => true
    List.ofFn (encodePair x w) = [false, true, false, false, true, true] ∧
    decodePair (encodePair x w) =
      some ((⟨2, x⟩, ⟨1, w⟩) : DecodedPair) := by
  dsimp
  constructor
  · rw [encodePair_toList]
    rfl
  · exact decodePair_roundtrip _ _

end Pnp3.Complexity.Uniform.V1.PairEncoding
