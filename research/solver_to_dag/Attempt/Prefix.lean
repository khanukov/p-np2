import Complexity.DagGadgets
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec

namespace Research.SolverToDag.Prefix
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.Frontier.ContractExpansion

/-- Out-of-bounds is a mismatch, never a padded input. -/
private def mismatch (W p : Nat) (b : Bool) : DagCircuit W :=
  if h : p < W then
    let neg := relabelInputs (fun _ : Fin 1 => ⟨p, h⟩) notCircuit
    withOutput neg (if b then neg.output else .input ⟨p, h⟩)
  else constCircuit W true

@[simp] private theorem restoreOutput {n : Nat} (c : DagCircuit n) : withOutput c c.output = c := by
  cases c
  rfl

private theorem mismatch_false (W p : Nat) (b : Bool) (bits : Bitstring W) :
    eval (mismatch W p b) bits = false ↔ ∃ h : p < W, bits ⟨p, h⟩ = b := by
  by_cases h : p < W
  · cases b <;> cases hb : bits ⟨p, h⟩ <;> simp [mismatch, h, hb]
  · simp [mismatch, h]

def fits {W : Nat} (bits : Bitstring W) (start : Nat) (word : List Bool) : Prop :=
  ∀ i : Fin word.length, ∃ h : start + i.val < W, bits ⟨start + i.val, h⟩ = word.get i

/-- Real physical bit tests for one grammar word at a specified cursor. -/
def wordCircuit (W start : Nat) (word : List Bool) : DagCircuit W :=
  substInputs notCircuit ![bigOrCircuit ((List.finRange word.length).map
    (fun i => mismatch W (start + i.val) (word.get i)))]

theorem wordCircuit_iff (W start : Nat) (word : List Bool) (bits : Bitstring W) :
    eval (wordCircuit W start word) bits = true ↔ fits bits start word := by
  simp [wordCircuit, fits, List.any_eq_false, mismatch_false]

@[simp] private theorem mismatch_gates (W p : Nat) (b : Bool) : (mismatch W p b).gates = 1 := by
  unfold mismatch
  split_ifs <;> rfl

@[simp] theorem wordCircuit_gates (W start : Nat) (word : List Bool) :
    (wordCircuit W start word).gates = 2 * word.length + 2 := by
  have hs : size (wordCircuit W start word) = 2 * word.length + 3 := by
    simp [wordCircuit, size_substInputs, bundleOfFamily_gates, bigOrCircuit_gates, Function.comp_def]
    omega
  change (wordCircuit W start word).gates + 1 = _ at hs
  omega

theorem fits_zero_prefix {W : Nat} (bits : Bitstring W) (word : List Bool) :
    fits bits 0 word ↔ word.IsPrefix (List.ofFn bits) := by
  constructor
  · intro h
    have hlen : word.length ≤ W := by
      by_cases hz : word.length = 0
      · omega
      · obtain ⟨hp, _⟩ := h ⟨word.length - 1, by omega⟩
        change 0 + (word.length - 1) < W at hp
        omega
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simpa using hlen, ?_⟩
    intro i hi
    obtain ⟨hp, he⟩ := h ⟨i, hi⟩
    simpa using he.symm
  · intro h i
    have hi : i.val < W := by have := h.length_le; simp only [List.length_ofFn] at this; omega
    refine ⟨by omega, ?_⟩
    have he := h.getElem i.isLt
    simpa using he.symm

theorem fits_cons {W : Nat} (bits : Bitstring W) (start : Nat) (b : Bool)
    (word : List Bool) :
    fits bits start (b :: word) ↔
      (∃ h : start < W, bits ⟨start, h⟩ = b) ∧ fits bits (start + 1) word := by
  simp [fits, Fin.forall_fin_succ, Nat.add_comm, Nat.add_left_comm]

theorem fits_append {W : Nat} (bits : Bitstring W) (start : Nat) (a b : List Bool) :
    fits bits start (a ++ b) ↔ fits bits start a ∧ fits bits (start + a.length) b := by
  induction a generalizing start with
  | nil => simp [fits]
  | cons c a ih =>
    simp only [List.cons_append, fits_cons, ih, List.length_cons]
    simp only [and_assoc, Nat.add_assoc, Nat.add_comm 1 a.length]

/-- A matched native word really is decoded, with its actual arbitrary tail.
This fixed-word feasibility lemma is NOT the arbitrary-witness parser. -/
theorem matched_native_decode {n W : Nat} (width : Nat) (hw : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) (bits : Bitstring W)
    (h : eval (wordCircuit W 0 (encodeCircuit width hw c)) bits = true) :
    ∃ tail, decodeCircuitFull n width (List.ofFn bits) = some (c, tail) := by
  have hp := (fits_zero_prefix bits _).mp ((wordCircuit_iff _ _ _ _).mp h)
  obtain ⟨tail, ht⟩ := hp
  rw [← ht]
  exact ⟨tail, decodeCircuitFull_encodeCircuit n width hw c tail⟩

end Research.SolverToDag.Prefix
