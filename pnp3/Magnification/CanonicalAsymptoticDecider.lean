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
