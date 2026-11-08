import Attempt.Parser
import Attempt.Leaves

namespace Research.SolverToDag.Codec
open Pnp4.Frontier.ContractExpansion
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Accepted fixed-width index payloads have exactly their native encoding. -/
private theorem encodeFin_of_decode (width : Nat) (bits : List Bool) (i : Fin (2 ^ width))
    (h : decodeFin width bits = some i) : encodeFin width i = bits := by
  induction width generalizing bits with
  | zero =>
    cases bits with
    | nil => rfl
    | cons b bs => simp [decodeFin] at h
  | succ width ih =>
    cases bits with
    | nil => simp [decodeFin] at h
    | cons b bs =>
      cases hd : decodeFin width bs with
      | none => simp [decodeFin, hd] at h
      | some j =>
        have hh := h
        simp only [decodeFin, hd, Option.some.injEq] at hh
        have hv := congrArg Fin.val hh
        have hb : decide (i.val % 2 = 1) = b := by
          cases b with
          | false =>
            change 0 + 2 * j.val = i.val at hv
            have hm : i.val % 2 = 0 := by omega
            simp [hm]
          | true =>
            change 1 + 2 * j.val = i.val at hv
            have hm : i.val % 2 = 1 := by omega
            simp [hm]
        have hj : i.val / 2 = j.val := by
          cases b with
          | false => change 0 + 2 * j.val = i.val at hv; omega
          | true => change 1 + 2 * j.val = i.val at hv; omega
        simp only [encodeFin, hb]
        congr 1
        have hf : (⟨i.val / 2, by rw [hj]; exact j.isLt⟩ : Fin (2 ^ width)) = j := Fin.ext hj
        simpa only [hf] using ih bs j hd

/-- Every successful native parse consumes precisely a native prefix word. -/
private theorem word_of_decode (n width depth : Nat) (hw : n ≤ 2 ^ width)
    (bits : List Bool) (c : CircuitTree n) (rest : List Bool)
    (h : decodeCircuitTreeAtDepth n width depth bits = some (c, rest)) :
    bits = encodeCircuitTree width hw c ++ rest := by
  induction depth generalizing bits c rest with
  | zero => simp [decodeCircuitTreeAtDepth] at h
  | succ depth ih =>
    cases bits with
    | nil => simp [decodeCircuitTreeAtDepth] at h
    | cons b bs =>
      cases bs with
      | nil => simp [decodeCircuitTreeAtDepth] at h
      | cons b' bs =>
        cases bs with
        | nil => simp [decodeCircuitTreeAtDepth] at h
        | cons b'' tail =>
          cases b <;> cases b' <;> cases b''
          all_goals try simp only [decodeCircuitTreeAtDepth] at h
          · split at h
            · contradiction
            · rename_i hl
              cases hd : decodeFin width (tail.take width) with
              | none => simp [hd] at h
              | some i =>
                simp only [hd] at h
                split at h
                · rename_i hv
                  cases h
                  have hi : (⟨i.val, by omega⟩ : Fin (2 ^ width)) = i := Fin.ext rfl
                  simp only [encodeCircuitTree, hi, encodeFin_of_decode width _ i hd]
                  exact congrArg (fun t => false :: false :: false :: t)
                    (List.take_append_drop width tail).symm
                · contradiction
          · cases tail with
            | nil => simp [decodeCircuitTreeAtDepth] at h
            | cons b tail => cases h; rfl
          · cases hd : decodeCircuitTreeAtDepth n width depth tail with
            | none => simp [hd] at h
            | some p =>
              rcases p with ⟨child, rem⟩
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simpa [encodeCircuitTree] using
                congrArg (fun t => false :: true :: false :: t) (ih tail child rem hd)
          all_goals
            first
            | contradiction
            | cases hl : decodeCircuitTreeAtDepth n width depth tail with
              | none => simp [hl] at h
              | some p =>
                rcases p with ⟨left, rem⟩
                simp only [hl] at h
                cases hr : decodeCircuitTreeAtDepth n width depth rem with
                | none => simp [hr] at h
                | some p =>
                  rcases p with ⟨right, rem'⟩
                  simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  simp [encodeCircuitTree, ih tail left rem hl,
                    ih rem right rem' hr, List.append_assoc]

/-- Exact native success, including any permitted ignored suffix. -/
private theorem native_word_of_decode (n width : Nat) (hw : n ≤ 2 ^ width)
    (bits : List Bool) (c : Pnp3.Models.Circuit n) (rest : List Bool)
    (h : decodeCircuitFull n width bits = some (c, rest)) :
    bits = encodeCircuit width hw c ++ rest := by
  unfold decodeCircuitFull decodeCircuit at h
  cases hd : decodeCircuitTreeAtDepth n width bits.length bits with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨tree, rem⟩
    simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa only [encodeCircuit, toTree_fromTree] using word_of_decode n width bits.length hw bits tree rem hd

/-- Actual bounded prefix-parser DAG, bound to the unchanged native decoder. -/
theorem parser_native_iff (n width W T : Nat) (hw : n ≤ 2 ^ width)
    (x : Pnp3.Core.BitVec n) (value : Bool) (bits : Bitstring W) :
    eval (Parser.acceptCircuit n width W T hw x value) bits = true ↔
      ∃ c rest, decodeCircuitFull n width (List.ofFn bits) = some (c, rest) ∧
        c.size ≤ T ∧ c.eval x = value := by
  rw [Parser.acceptCircuit_iff]
  constructor
  · rintro ⟨c, hc, hf, he⟩
    obtain ⟨rest, hd⟩ := Prefix.matched_native_decode width hw c bits
      ((Prefix.wordCircuit_iff _ _ _ _).mpr hf)
    exact ⟨c, rest, hd, hc, he⟩
  · rintro ⟨c, rest, hd, hc, he⟩
    refine ⟨c, hc, (Prefix.fits_zero_prefix bits _).mpr ?_, he⟩
    exact ⟨rest, (native_word_of_decode n width hw _ c rest hd).symm⟩

/-- One concrete table position; MUX uses the real table bit, never a promise. -/
private def position (n width W T : Nat) (hw : n ≤ 2 ^ width)
    (j : Fin (Pnp3.Models.Partial.tableLen n)) :
    DagCircuit (Pnp3.Models.Partial.tableLen n + W) :=
  substInputs muxCircuit ![inputProj (Fin.castAdd W j),
    relabelInputs (Fin.natAdd (Pnp3.Models.Partial.tableLen n))
      (Parser.acceptCircuit n width W T hw (Pnp3.Core.vecOfNat n j.val) true),
    relabelInputs (Fin.natAdd (Pnp3.Models.Partial.tableLen n))
      (Parser.acceptCircuit n width W T hw (Pnp3.Core.vecOfNat n j.val) false)]

private theorem position_iff (n width W T : Nat) (hw : n ≤ 2 ^ width)
    (j : Fin (Pnp3.Models.Partial.tableLen n))
    (tt : Bitstring (Pnp3.Models.Partial.tableLen n)) (bits : Bitstring W) :
    eval (position n width W T hw j) (Fin.addCases tt bits) = true ↔
      ∃ c rest, decodeCircuitFull n width (List.ofFn bits) = some (c, rest) ∧
        c.size ≤ T ∧ c.eval (Pnp3.Core.vecOfNat n j.val) = tt j := by
  have he : eval (position n width W T hw j) (Fin.addCases tt bits) =
      if tt j then eval (Parser.acceptCircuit n width W T hw (Pnp3.Core.vecOfNat n j.val) true) bits
      else eval (Parser.acceptCircuit n width W T hw (Pnp3.Core.vecOfNat n j.val) false) bits := by
    simp [position]
  rw [he]
  cases tt j <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    exact parser_native_iff n width W T hw _ _ bits

/-- Check the same decoded TREE at every one of N assignments and the whole table. -/
private def verifier (n width W T : Nat) (hw : n ≤ 2 ^ width) :
    DagCircuit (Pnp3.Models.Partial.tableLen n + W) :=
  substInputs notCircuit ![bigOrCircuit ((List.finRange (Pnp3.Models.Partial.tableLen n)).map
    (fun j => substInputs notCircuit ![position n width W T hw j]))]

private theorem verifier_iff (n width W T : Nat) (hw : n ≤ 2 ^ width)
    (tt : Bitstring (Pnp3.Models.Partial.tableLen n)) (bits : Bitstring W) :
    eval (verifier n width W T hw) (Fin.addCases tt bits) = true ↔
      ∃ c rest, decodeCircuitFull n width (List.ofFn bits) = some (c, rest) ∧
        c.size ≤ T ∧ tt = treeTable c := by
  have hall : eval (verifier n width W T hw) (Fin.addCases tt bits) = true ↔
      ∀ j : Fin (Pnp3.Models.Partial.tableLen n),
        eval (position n width W T hw j) (Fin.addCases tt bits) = true := by
    simp [verifier, List.any_eq_false]
  rw [hall]
  constructor
  · intro h
    obtain ⟨c, rest, hd, hc, _⟩ := (position_iff n width W T hw
      ⟨0, by exact Nat.two_pow_pos _⟩ tt bits).mp (h ⟨0, Nat.two_pow_pos _⟩)
    refine ⟨c, rest, hd, hc, funext (fun j => ?_)⟩
    obtain ⟨c', rest', hd', _, he⟩ := (position_iff n width W T hw j tt bits).mp (h j)
    have hi := hd.symm.trans hd'
    cases Option.some.inj hi
    exact he.symm
  · rintro ⟨c, rest, hd, hc, rfl⟩ j
    exact (position_iff n width W T hw j _ bits).mpr ⟨c, rest, hd, hc, rfl⟩

private theorem position_size (n width W T : Nat) (hw : n ≤ 2 ^ width)
    (j : Fin (Pnp3.Models.Partial.tableLen n)) :
    size (position n width W T hw j) ≤ 2 * Parser.gateBudget n width W T + 5 := by
  have h0 := Parser.acceptCircuit_size n width W T hw (Pnp3.Core.vecOfNat n j.val) false
  have h1 := Parser.acceptCircuit_size n width W T hw (Pnp3.Core.vecOfNat n j.val) true
  have he : size (position n width W T hw j) =
      (Parser.acceptCircuit n width W T hw (Pnp3.Core.vecOfNat n j.val) true).gates +
      (Parser.acceptCircuit n width W T hw (Pnp3.Core.vecOfNat n j.val) false).gates + 5 := by
    simp [position, size_substInputs, bundleOfFamily_gates, Fin.sum_univ_succ, relabelInputs, inputProj]
  rw [he]
  change _ + 1 ≤ _ at h0 h1
  omega

@[simp] private theorem not_gates {q : Nat} (c : DagCircuit q) :
    (substInputs notCircuit ![c]).gates = c.gates + 1 := by
  have h : size (substInputs notCircuit ![c]) = c.gates + 2 := by
    simp [size_substInputs, bundleOfFamily_gates]
  change _ + 1 = _ at h
  omega

private theorem map_sum_le {α : Type} (xs : List α) (f : α → Nat) (b : Nat)
    (h : ∀ a ∈ xs, f a ≤ b) : (xs.map f).sum ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hh := ih (fun v hv => h v (by simp [hv]))
    have ha := h a (by simp)
    nlinarith

private def verifierBudget (n width W T : Nat) : Nat :=
  Pnp3.Models.Partial.tableLen n * (2 * Parser.gateBudget n width W T + 6) + 3

private theorem verifier_size (n width W T : Nat) (hw : n ≤ 2 ^ width) :
    size (verifier n width W T hw) ≤ verifierBudget n width W T := by
  have hs := map_sum_le (List.finRange (Pnp3.Models.Partial.tableLen n))
    (fun j => (position n width W T hw j).gates + 2) (2 * Parser.gateBudget n width W T + 6)
    (fun j _ => by
      have h := position_size n width W T hw j
      change _ + 1 ≤ _ at h
      change (position n width W T hw j).gates + 2 ≤ _
      omega)
  simp only [List.length_finRange] at hs
  have he : size (verifier n width W T hw) =
      ((List.finRange (Pnp3.Models.Partial.tableLen n)).map
        (fun j => (position n width W T hw j).gates + 2)).sum + 3 := by
    simp [verifier, size_substInputs, bundleOfFamily_gates, bigOrCircuit_gates,
      List.map_map, Function.comp_def, List.sum_map_add]
    omega
  rw [he]
  exact Nat.add_le_add_right hs 3

/-- The actual concrete-codec head graph; no verifier/provider field. -/
def head (k n : Nat) : DagCircuit (Pnp3.Models.Partial.tableLen n + witnessWidth k n) :=
  verifier n (bitLength n) (witnessWidth k n) (thresholdPoly k n)
    (Nat.le_of_lt (nat_lt_two_pow_bitLength n))

theorem head_iff (k n : Nat) (tt : Pnp4.AlgorithmsToLowerBounds.TruthTable n)
    (bits : Bitstring (witnessWidth k n)) :
    eval (head k n) (Fin.addCases tt bits) = true ↔
      (treeCircuitWitnessCodec (thresholdPoly k)).verifies n tt bits := by
  rw [head, verifier_iff]
  simp only [Pnp4.Frontier.TreeCircuitWitnessCodec.verifies, computes_iff_table]
  change (∃ c rest, decodeCircuitFull n (bitLength n) (List.ofFn bits) = some (c, rest) ∧
    c.size ≤ thresholdPoly k n ∧ tt = treeTable c) ↔
    ∃ c, (decodeCircuitFull n (bitLength n) (List.ofFn bits)).map Prod.fst = some c ∧
      c.size ≤ thresholdPoly k n ∧ tt = treeTable c
  constructor
  · rintro ⟨c, rest, hd, hc, he⟩
    exact ⟨c, by rw [hd]; rfl, hc, he⟩
  · rintro ⟨c, hd, hc, he⟩
    cases h : decodeCircuitFull n (bitLength n) (List.ofFn bits) with
    | none => simp [h] at hd
    | some p =>
      rcases p with ⟨c', rest⟩
      simp only [h, Option.map_some, Option.some.injEq] at hd
      subst c'
      exact ⟨c, rest, rfl, hc, he⟩

/-- Real single-output recognizer assembled from every solver output DAG. -/
def recognizer {k d : Nat} (S : ConcreteSolver k d) (n : Nat) :
    DagCircuit (Pnp3.Models.Partial.tableLen n) := plugSolver S n (head k n)

theorem recognizer_iff {k d : Nat} (S : ConcreteSolver k d) (n : Nat)
    (tt : Pnp4.AlgorithmsToLowerBounds.TruthTable n) :
    eval (recognizer S n) tt = true ↔
      Pnp4.AlgorithmsToLowerBounds.treeMCSPPredicate n (thresholdPoly k n) tt := by
  rw [recognizer, plugSolver_eval, head_iff]
  constructor
  · exact (treeCircuitWitnessCodec (thresholdPoly k)).sound n tt _
  · exact S.solves n tt

/-- Explicit arithmetic price, including output+1 and EVERY solver bit graph. -/
theorem recognizer_size_le {k d : Nat} (S : ConcreteSolver k d) (n : Nat) :
    size (recognizer S n) ≤ Pnp3.Models.Partial.tableLen n *
      (2 * Parser.gateBudget n (bitLength n) ((bitLength n + 4) * (n ^ k + k)) (n ^ k + k) + 6) +
      3 + ((bitLength n + 4) * (n ^ k + k)) * (Pnp3.Models.Partial.tableLen n ^ d + d) := by
  apply (plugSolver_size_le S n (head k n)).trans
  exact Nat.add_le_add_right
    (verifier_size n (bitLength n) (witnessWidth k n) (thresholdPoly k n)
      (Nat.le_of_lt (nat_lt_two_pow_bitLength n))) _

theorem recognizer_polynomial (k d : Nat) :
    ∃ e : Nat, ∀ (S : ConcreteSolver k d) (n : Nat),
      size (recognizer S n) ≤ Pnp3.Models.Partial.tableLen n ^ e + e := by
  have hv := (polyBoundedInTable_tableLen.mul
    (((PolyBoundedInTable.const 2).mul (Parser.gateBudget_polynomial k)).add
      (PolyBoundedInTable.const 6))).add (PolyBoundedInTable.const 3)
  have hw := polyBoundedInTable_treeWitnessBits_of_thresholdPoly _ (polyBoundedInTable_thresholdPoly k)
  have hb := (PolyBoundedInTable.tableLen_pow d).add (PolyBoundedInTable.const d)
  obtain ⟨e, he⟩ := (hv.add (hw.mul hb)).powAdd
  refine ⟨e, fun S n => (plugSolver_size_le S n (head k n)).trans ?_⟩
  have hs := verifier_size n (bitLength n) (witnessWidth k n) (thresholdPoly k n)
    (Nat.le_of_lt (nat_lt_two_pow_bitLength n))
  exact (Nat.add_le_add_right hs (witnessWidth k n * solverBudget d n)).trans (he n)

/-- Closed semantics AND polynomial size, with e depending only on fixed k,d. -/
theorem solver_to_dag_capstone (k d : Nat) :
    ∃ e : Nat, ∀ (S : ConcreteSolver k d) (n : Nat),
      (∀ tt, eval (recognizer S n) tt = true ↔
        Pnp4.AlgorithmsToLowerBounds.treeMCSPPredicate n (thresholdPoly k n) tt) ∧
      size (recognizer S n) ≤ Pnp3.Models.Partial.tableLen n ^ e + e := by
  obtain ⟨e, he⟩ := recognizer_polynomial k d
  exact ⟨e, fun S n => ⟨recognizer_iff S n, he S n⟩⟩

end Research.SolverToDag.Codec
