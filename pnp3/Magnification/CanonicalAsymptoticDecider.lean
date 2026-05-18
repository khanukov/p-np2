import Magnification.CanonicalAsymptoticTrackData

/-!
# Canonical asymptotic decider and verifier-components bridge

This module reduces the canonical TM-verifier obligation to a
**single typed sub-obligation** by:

1. Defining a **computable** Boolean decision procedure
   `decideAsymptotic : (n : Nat) → Bitstring n → Bool` that matches
   `gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec` exactly.
2. Exposing a structure `CanonicalAsymptoticVerifierComponents` packaging
   a concrete TM whose acceptance behaviour matches `decideAsymptotic`.
3. Building `witnessOfComponents : Components →
   GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.

The mathematical content is split cleanly:

* **Decidability + correctness of `decideAsymptotic`**: closed
  unconditionally in this module.
* **Constructing the TM with the matching acceptance behaviour**: the
  remaining engineering obligation (scaffolded in
  `pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean`).

For `canonicalAsymptoticSpec` (with `sYES n = 1`), the YES-predicate at
slice `m` is "exists a size-`≤ 1` circuit consistent with the partial
truth table".  Size-1 circuits over `m` variables are exactly the
`m + 2` candidates `Circuit.const false`, `Circuit.const true`, and
`Circuit.input i` for `i : Fin m`.  This bounded enumeration gives the
decider.
-/

namespace Pnp3
namespace Magnification

open Models
open Core
open ComplexityInterfaces
open Internal.PsubsetPpoly

/-! ## Size-≤-1 circuit enumeration -/

/-- All circuits of size exactly 1 over `m` variables. -/
def size1Candidates (m : Nat) : List (Circuit m) :=
  Circuit.const false :: Circuit.const true ::
    (List.finRange m).map Circuit.input

@[simp] lemma mem_size1Candidates_const (m : Nat) (b : Bool) :
    Circuit.const b ∈ size1Candidates m := by
  cases b
  · exact List.mem_cons_self
  · refine List.mem_cons.mpr (Or.inr ?_)
    exact List.mem_cons_self

@[simp] lemma mem_size1Candidates_input (m : Nat) (i : Fin m) :
    Circuit.input i ∈ size1Candidates m := by
  refine List.mem_cons.mpr (Or.inr ?_)
  refine List.mem_cons.mpr (Or.inr ?_)
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- Every member of `size1Candidates m` has `Circuit.size = 1`. -/
lemma size1Candidates_size_eq_one {m : Nat} {C : Circuit m}
    (hC : C ∈ size1Candidates m) : C.size = 1 := by
  rcases List.mem_cons.mp hC with rfl | h
  · simp [Circuit.size]
  · rcases List.mem_cons.mp h with rfl | h2
    · simp [Circuit.size]
    · rcases List.mem_map.mp h2 with ⟨_, _, rfl⟩
      simp [Circuit.size]

/-- Every circuit has size at least one. -/
private lemma Circuit.one_le_size {m : Nat} (c : Circuit m) : 1 ≤ c.size := by
  induction c with
  | input _ => simp [Circuit.size]
  | const _ => simp [Circuit.size]
  | not c ih => simp [Circuit.size]
  | and c1 c2 _ _ => simp [Circuit.size]
  | or c1 c2 _ _ => simp [Circuit.size]

/-- Every size-≤-1 circuit is in `size1Candidates`. -/
lemma mem_size1Candidates_of_size_le_one {m : Nat} (C : Circuit m)
    (h : C.size ≤ 1) : C ∈ size1Candidates m := by
  cases C with
  | input i => exact mem_size1Candidates_input m i
  | const b => exact mem_size1Candidates_const m b
  | not c =>
    exfalso
    have hc : 1 ≤ c.size := Circuit.one_le_size c
    simp [Circuit.size] at h
    omega
  | and c1 c2 =>
    exfalso
    have h1 : 1 ≤ c1.size := Circuit.one_le_size c1
    have h2 : 1 ≤ c2.size := Circuit.one_le_size c2
    simp [Circuit.size] at h
    omega
  | or c1 c2 =>
    exfalso
    have h1 : 1 ≤ c1.size := Circuit.one_le_size c1
    have h2 : 1 ≤ c2.size := Circuit.one_le_size c2
    simp [Circuit.size] at h
    omega

/-! ## Decider for `PartialMCSP_YES_at m 1` -/

/-- Computable Boolean decider for `PartialMCSP_YES_at m 1 T`. -/
def decideYesAt1 (m : Nat) (T : PartialTruthTable m) : Bool :=
  (size1Candidates m).any (fun C => is_consistent_bool C T)

theorem decideYesAt1_iff (m : Nat) (T : PartialTruthTable m) :
    decideYesAt1 m T = true ↔ PartialMCSP_YES_at m 1 T := by
  unfold decideYesAt1
  constructor
  · intro h
    rcases List.any_eq_true.mp h with ⟨C, hMem, hBool⟩
    have hSize : C.size = 1 := size1Candidates_size_eq_one hMem
    have hCons : Models.is_consistent C T :=
      (is_consistent_iff_bool C T).mpr hBool
    exact ⟨C, by rw [hSize], hCons⟩
  · rintro ⟨C, hSize, hCons⟩
    refine List.any_eq_true.mpr ⟨C, ?_, ?_⟩
    · exact mem_size1Candidates_of_size_le_one C hSize
    · exact (is_consistent_iff_bool C T).mp hCons

/-! ## Canonical slice detection

For canonical input length `N = Partial.inputLen m = 2 · 2^m`, find `m`.
We use bounded `List.find?` enumeration; since `2 · 2^m > m`, every
valid slice index satisfies `m ≤ N`.
-/

/-- Find `m` such that `N = Partial.inputLen m`, if any. -/
def findCanonicalSlice (N : Nat) : Option Nat :=
  (List.range (N + 1)).find? (fun m => decide (Partial.inputLen m = N))

private lemma le_partialInputLen (m : Nat) : m < Partial.inputLen m := by
  show m < 2 * Partial.tableLen m
  have hpow : m < Partial.tableLen m := by
    show m < 2 ^ m
    exact Nat.lt_two_pow_self
  have hpos : 0 < Partial.tableLen m := by
    show 0 < 2 ^ m
    exact Nat.two_pow_pos m
  omega

lemma findCanonicalSlice_eq_some_iff (N m : Nat) :
    findCanonicalSlice N = some m ↔ N = Partial.inputLen m := by
  unfold findCanonicalSlice
  constructor
  · intro h
    have hSpec := List.find?_eq_some_iff_getElem.mp h
    -- hSpec : decide (Partial.inputLen m = N) = true ∧ ∃ i hi, ...
    exact (decide_eq_true_eq.mp hSpec.1).symm
  · intro hEq
    have hmlt : m < N + 1 := by
      rw [hEq]
      have := le_partialInputLen m
      omega
    have hmem : m ∈ List.range (N + 1) := List.mem_range.mpr hmlt
    have hpred : decide (Partial.inputLen m = N) = true := decide_eq_true hEq.symm
    -- The find? returns some m' (any m' satisfying the predicate has Partial.inputLen m' = N).
    set p : Nat → Bool := fun m' => decide (Partial.inputLen m' = N) with hp_def
    have hfind_some : (List.range (N + 1)).find? p ≠ none := by
      intro hnone
      have hnotP := List.find?_eq_none.mp hnone m hmem
      have : p m = true := hpred
      exact absurd this (by simp [hnotP])
    rcases Option.ne_none_iff_exists'.mp hfind_some with ⟨m', hm'⟩
    rw [hm']
    have hSpec := List.find?_eq_some_iff_getElem.mp hm'
    have hEq' : Partial.inputLen m' = N := decide_eq_true_eq.mp hSpec.1
    -- Both Partial.inputLen m and Partial.inputLen m' equal N, so m = m' by injectivity.
    have hLensEq : Partial.inputLen m = Partial.inputLen m' := by rw [← hEq, hEq']
    have hmEq : m = m' := Models.partialInputLen_injective hLensEq
    rw [hmEq]

lemma findCanonicalSlice_eq_none_iff (N : Nat) :
    findCanonicalSlice N = none ↔ ¬ ∃ m, N = Partial.inputLen m := by
  constructor
  · intro h ⟨m, hEq⟩
    have : findCanonicalSlice N = some m := (findCanonicalSlice_eq_some_iff N m).mpr hEq
    rw [this] at h
    exact Option.noConfusion h
  · intro h
    by_contra hne
    rcases Option.ne_none_iff_exists'.mp hne with ⟨m, hSome⟩
    have hEq : N = Partial.inputLen m := (findCanonicalSlice_eq_some_iff N m).mp hSome
    exact h ⟨m, hEq⟩

/-! ## Asymptotic decider -/

/-- Computable decider matching `gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec`.

Returns `false` at non-canonical input lengths.  At canonical length
`N = Partial.inputLen m`, enumerates the `m + 2` size-1 candidates and
checks consistency with `decodePartial x`. -/
def decideAsymptotic (N : Nat) (x : Bitstring N) : Bool :=
  match h : findCanonicalSlice N with
  | none => false
  | some m =>
    have hEq : N = Partial.inputLen m :=
      (findCanonicalSlice_eq_some_iff N m).mp h
    decideYesAt1 m (decodePartial (hEq ▸ x : Core.BitVec (Partial.inputLen m)))

/-- At canonical length, `decideAsymptotic` agrees with the slice-1 decider. -/
theorem decideAsymptotic_at_inputLen (m : Nat) (x : Bitstring (Partial.inputLen m)) :
    decideAsymptotic (Partial.inputLen m) x =
      decideYesAt1 m (decodePartial (x : Core.BitVec (Partial.inputLen m))) := by
  unfold decideAsymptotic
  have hFind : findCanonicalSlice (Partial.inputLen m) = some m :=
    (findCanonicalSlice_eq_some_iff _ _).mpr rfl
  split
  · rename_i heq
    rw [heq] at hFind
    cases hFind
  · rename_i m' heq
    rw [hFind] at heq
    have hmEq : m = m' := Option.some.inj heq
    subst hmEq
    rfl

/-- At non-canonical length, `decideAsymptotic` returns `false`. -/
theorem decideAsymptotic_of_not_canonical (N : Nat) (x : Bitstring N)
    (h : ¬ ∃ m, N = Partial.inputLen m) :
    decideAsymptotic N x = false := by
  unfold decideAsymptotic
  have hFind : findCanonicalSlice N = none :=
    (findCanonicalSlice_eq_none_iff N).mpr h
  split
  · rfl
  · rename_i m' heq
    rw [hFind] at heq
    cases heq

/-- At non-canonical length, the language returns `false`. -/
theorem gapPartialMCSP_AsymptoticLanguage_of_not_canonical
    (N : Nat) (x : Bitstring N) (h : ¬ ∃ m, N = Partial.inputLen m) :
    gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec N x = false := by
  classical
  unfold gapPartialMCSP_AsymptoticLanguage
  simp only [h, dif_neg, not_false_iff]

/-- Correctness of `decideAsymptotic` vs the canonical asymptotic language. -/
theorem decideAsymptotic_iff (N : Nat) (x : Bitstring N) :
    decideAsymptotic N x = true ↔
      gapPartialMCSP_AsymptoticLanguage canonicalAsymptoticSpec N x = true := by
  by_cases h : ∃ m, N = Partial.inputLen m
  · obtain ⟨m, hEq⟩ := h
    subst hEq
    -- Now N = Partial.inputLen m, everything reduces cleanly.
    rw [decideAsymptotic_at_inputLen]
    rw [decideYesAt1_iff]
    have := Models.gapPartialMCSP_asymptoticLanguage_apply_inputLen
      canonicalAsymptoticSpec m x
    rw [this]
    -- sYES m = 1
    show PartialMCSP_YES_at m 1 (decodePartial x) ↔
      PartialMCSP_YES_at m (canonicalAsymptoticSpec.sYES m) (decodePartial x)
    rfl
  · rw [decideAsymptotic_of_not_canonical N x h]
    rw [gapPartialMCSP_AsymptoticLanguage_of_not_canonical N x h]

/-! ## Concrete decidability facts (placeholder-free leaves)

These lemmas characterise `decideAsymptotic` on common non-canonical
lengths.  They are used as building blocks for the eventual
TM-verifier correctness, and demonstrate that the decider terminates
on concrete inputs.
-/

/-- Lower bound: every canonical input length is at least 2. -/
private lemma partialInputLen_ge_two (m : Nat) : 2 ≤ Partial.inputLen m := by
  show 2 ≤ 2 * Partial.tableLen m
  have hpos : 1 ≤ Partial.tableLen m := by
    show 1 ≤ 2 ^ m
    exact Nat.one_le_two_pow
  omega

/-- At non-canonical length `0`, the asymptotic language is `false`. -/
theorem decideAsymptotic_at_zero (x : Bitstring 0) :
    decideAsymptotic 0 x = false := by
  apply decideAsymptotic_of_not_canonical
  rintro ⟨m, hEq⟩
  have := partialInputLen_ge_two m
  omega

/-- At non-canonical length `1`, the asymptotic language is `false`. -/
theorem decideAsymptotic_at_one (x : Bitstring 1) :
    decideAsymptotic 1 x = false := by
  apply decideAsymptotic_of_not_canonical
  rintro ⟨m, hEq⟩
  have := partialInputLen_ge_two m
  omega

/-- At non-canonical length `3`, the asymptotic language is `false`.
Demonstrates the decider correctly rejects odd lengths between
consecutive canonical points (`2 < 3 < 4`). -/
theorem decideAsymptotic_at_three (x : Bitstring 3) :
    decideAsymptotic 3 x = false := by
  apply decideAsymptotic_of_not_canonical
  rintro ⟨m, hEq⟩
  match m, hEq with
  | 0, h => exact absurd h (by decide)
  | m + 1, h =>
    have hlb : 4 ≤ Partial.inputLen (m + 1) := by
      show 4 ≤ 2 * Partial.tableLen (m + 1)
      have : 2 ≤ Partial.tableLen (m + 1) := by
        show 2 ≤ 2 ^ (m + 1)
        calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega

/-- At canonical length `2 = Partial.inputLen 0`, the asymptotic
language is **always true**: with `m = 0` variables, the partial truth
table has a single row, and one of `Circuit.const false` or
`Circuit.const true` matches it (vacuously when the row is `none`, or
exactly when the row is `some b`). -/
theorem decideYesAt1_zero_always_true (T : PartialTruthTable 0) :
    decideYesAt1 0 T = true := by
  unfold decideYesAt1
  apply List.any_eq_true.mpr
  -- The partial table has exactly one row (Fin (Partial.tableLen 0) = Fin 1).
  -- Choose the matching constant.
  cases hT : T ⟨0, by decide⟩ with
  | none =>
    refine ⟨Circuit.const false, mem_size1Candidates_const 0 false, ?_⟩
    unfold is_consistent_bool
    apply List.all_eq_true.mpr
    intro i _
    have hi : i = ⟨0, by decide⟩ := by
      have hsub : Subsingleton (Fin (Partial.tableLen 0)) := by
        show Subsingleton (Fin 1); infer_instance
      exact hsub.elim _ _
    subst hi
    rw [hT]
  | some b =>
    refine ⟨Circuit.const b, mem_size1Candidates_const 0 b, ?_⟩
    unfold is_consistent_bool
    apply List.all_eq_true.mpr
    intro i _
    have hi : i = ⟨0, by decide⟩ := by
      have hsub : Subsingleton (Fin (Partial.tableLen 0)) := by
        show Subsingleton (Fin 1); infer_instance
      exact hsub.elim _ _
    subst hi
    rw [hT]
    simp [Circuit.eval]

/-- At canonical length `2`, the asymptotic language is `true` for any
input.  This is the smallest canonical slice (`m = 0`), and shows the
decider correctly accepts all canonical-length-2 inputs. -/
theorem decideAsymptotic_at_two (x : Bitstring 2) :
    decideAsymptotic 2 x = true := by
  -- 2 = Partial.inputLen 0 definitionally.
  have heq : decideAsymptotic 2 x = decideAsymptotic (Partial.inputLen 0) x := rfl
  rw [heq, decideAsymptotic_at_inputLen]
  exact decideYesAt1_zero_always_true _

/-! ## Slice m=1: a concrete NO instance

At m=1, `size1Candidates 1 = [const false, const true, input 0]`.
The slice fails (`decideYesAt1 1 T = false`) exactly when both
constants are inconsistent (table contains both `some true` and
`some false`) AND the input-0 circuit is inconsistent (specifically:
T 0 = some true OR T 1 = some false).

The simplest concrete NO instance: T 0 = some true, T 1 = some false.
This makes all three size-1 candidates fail simultaneously.
-/

/-- `Circuit.const false` is inconsistent with any table that has a
`some true` cell. -/
private lemma not_consistent_const_false_at_one
    (T : PartialTruthTable 1) (h : T ⟨0, by decide⟩ = some true) :
    ¬ is_consistent (Circuit.const false) T := by
  intro hc
  have hidx : assignmentIndex (Core.vecOfNat 1 0) = ⟨0, by decide⟩ := by
    ext; show 0 % _ = 0; decide
  have hat := hc (Core.vecOfNat 1 0)
  rw [hidx, h] at hat
  simp [Circuit.eval] at hat

/-- `Circuit.const true` is inconsistent with any table that has a
`some false` cell. -/
private lemma not_consistent_const_true_at_one
    (T : PartialTruthTable 1) (h : T ⟨1, by decide⟩ = some false) :
    ¬ is_consistent (Circuit.const true) T := by
  intro hc
  have hidx : assignmentIndex (Core.vecOfNat 1 1) = ⟨1, by decide⟩ := by
    ext
    show bitVecToNat (Core.vecOfNat 1 1) % Partial.tableLen 1 = 1
    have hbn := bitVecToNat_vecOfNat (n := 1) (m := 1) (by decide)
    rw [hbn]; decide
  have hat := hc (Core.vecOfNat 1 1)
  rw [hidx, h] at hat
  simp [Circuit.eval] at hat

/-- `Circuit.input 0` is inconsistent if `T 0 = some true`
(since `(input 0).eval (vecOfNat 1 0) = false ≠ true`). -/
private lemma not_consistent_input_zero_at_one
    (T : PartialTruthTable 1) (h : T ⟨0, by decide⟩ = some true) :
    ¬ is_consistent (Circuit.input (⟨0, by decide⟩ : Fin 1)) T := by
  intro hc
  have hidx : assignmentIndex (Core.vecOfNat 1 0) = ⟨0, by decide⟩ := by
    ext; show 0 % _ = 0; decide
  have hat := hc (Core.vecOfNat 1 0)
  rw [hidx, h] at hat
  -- hat : Circuit.eval (input ⟨0,_⟩) (vecOfNat 1 0) = true
  -- (input k).eval x = x k
  have hev : Circuit.eval (Circuit.input (⟨0, by decide⟩ : Fin 1))
      (Core.vecOfNat 1 0) = false := by
    show Core.vecOfNat 1 0 ⟨0, by decide⟩ = false
    show Nat.testBit 0 0 = false
    decide
  rw [hev] at hat
  exact Bool.false_ne_true hat

/-- Concrete NO witness at `m = 1`: if T 0 = some true and
T 1 = some false, then no size-1 circuit is consistent with T. -/
theorem decideYesAt1_one_NO_case
    (T : PartialTruthTable 1)
    (h0 : T ⟨0, by decide⟩ = some true)
    (h1 : T ⟨1, by decide⟩ = some false) :
    decideYesAt1 1 T = false := by
  by_contra hne
  have hne' : decideYesAt1 1 T ≠ false := hne
  -- decideYesAt1 1 T must be true; extract a consistent size-1 candidate
  cases hT : decideYesAt1 1 T with
  | false => exact hne' hT
  | true =>
    rcases (decideYesAt1_iff 1 T).mp hT with ⟨C, hSize, hCons⟩
    have hMem : C ∈ size1Candidates 1 :=
      mem_size1Candidates_of_size_le_one C hSize
    -- C is one of: const false, const true, input ⟨0, _⟩.
    rcases List.mem_cons.mp hMem with rfl | hrest
    · exact not_consistent_const_false_at_one T h0 hCons
    rcases List.mem_cons.mp hrest with rfl | hrest2
    · exact not_consistent_const_true_at_one T h1 hCons
    rcases List.mem_map.mp hrest2 with ⟨i, _, hi⟩
    -- i : Fin 1, so i = ⟨0, _⟩.  Then C = Circuit.input i.
    have hi_eq : i = ⟨0, by decide⟩ := by
      have hsub : Subsingleton (Fin 1) := by infer_instance
      exact hsub.elim _ _
    subst hi_eq
    rw [← hi] at hCons
    exact not_consistent_input_zero_at_one T h0 hCons

/-! ## Verifier-components bridge

A `CanonicalAsymptoticVerifierComponents` packages a TM whose acceptance
on `(x ++ w)` matches `decideAsymptotic N x` for every certificate `w`.
This is the **minimum sufficient condition** for the witness package
required by `canonicalAsymptoticData_of_TM`.

The plan for closing this is documented in
`pnp3/Docs/TMVerifier_Session_Plan.md` — a 7-session decomposition
totalling ~2500 LOC of TM-engineering with 0 sorries per session. -/

/-- Components sufficient to build the canonical asymptotic NP witness. -/
structure CanonicalAsymptoticVerifierComponents where
  /-- The verifier TM. -/
  M : Internal.PsubsetPpoly.TM.{0}
  /-- Runtime polynomial exponent. -/
  c : Nat
  /-- Certificate-length polynomial exponent. -/
  k : Nat
  /-- Polynomial-runtime bound. -/
  runTime_poly : ∀ n,
    M.runTime (n + certificateLength n k) ≤
      (n + certificateLength n k) ^ c + c
  /-- The TM's acceptance on `(x ++ w)` matches `decideAsymptotic`,
      independently of the certificate `w`. -/
  accepts_eq : ∀ n (x : Bitstring n) (w : Bitstring (certificateLength n k)),
    Internal.PsubsetPpoly.TM.accepts
      (M := M)
      (n := n + certificateLength n k)
      (concatBitstring x w) = decideAsymptotic n x

namespace CanonicalAsymptoticVerifierComponents

/-- The trivial certificate (constant `false`) of any length. -/
def trivialCert (k : Nat) : Bitstring k := fun _ => false

/-- Bridge: a verifier-components package yields a full TM witness. -/
def witness (V : CanonicalAsymptoticVerifierComponents) :
    Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec where
  M := V.M
  c := V.c
  k := V.k
  runTime_poly := V.runTime_poly
  correct := by
    intro n x
    rw [← decideAsymptotic_iff]
    constructor
    · intro h
      refine ⟨trivialCert _, ?_⟩
      rw [V.accepts_eq]
      exact h
    · rintro ⟨w, hw⟩
      rw [V.accepts_eq] at hw
      exact hw

end CanonicalAsymptoticVerifierComponents

/-! ## Composed bridge: from components straight to the strict NP package -/

/-- From verifier-components, produce the full `AntiCheckerAssumptions`
package (i.e., everything downstream consumers of the canonical track
need). -/
def canonicalAntiCheckerAssumptions_of_components
    (V : CanonicalAsymptoticVerifierComponents) :
    AntiCheckerAssumptions :=
  canonicalAntiCheckerAssumptions_of_TM
    (CanonicalAsymptoticVerifierComponents.witness V)

/-- From verifier-components, produce the `AsymptoticNPPullback`. -/
def canonicalAsymptoticNPBridge_of_components
    (V : CanonicalAsymptoticVerifierComponents) :
    AsymptoticNPPullback canonicalAsymptoticHAsym :=
  canonicalAsymptoticNPBridge_of_TM
    (CanonicalAsymptoticVerifierComponents.witness V)

/-- From verifier-components, produce the `AsymptoticFormulaTrackData`. -/
def canonicalAsymptoticData_of_components
    (V : CanonicalAsymptoticVerifierComponents) :
    AsymptoticFormulaTrackData :=
  canonicalAsymptoticData_of_TM
    (CanonicalAsymptoticVerifierComponents.witness V)

end Magnification
end Pnp3
