import Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP
import Counting.Count_EasyFuncs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Uniform acceptance probability of a Boolean predicate over all `m`-bit strings.

This is the natural probability measure for the local-PRG route: sample the
input uniformly from the full truth-table cube.
-/
noncomputable def bitVecAcceptanceProbability
    {m : Nat}
    (A : BitVec m → Bool) : Rat :=
  (((Finset.univ.filter fun x : BitVec m => A x = true).card : Rat) /
    (2 ^ m : Rat))

/-- Uniform acceptance probability over the truth-table cube on `n` variables. -/
noncomputable def uniformTruthTableAcceptanceProbability
    {n : Nat}
    (A : TruthTable n → Bool) : Rat :=
  bitVecAcceptanceProbability A

/--
Truth-table local-PRG surface for the `pnp4` track.

At this stage we only record the output distribution and the crucial
"easy-image" fact that every generated truth table lies below some fixed tree
MCSP threshold.  Explicit locality certificates can be layered in later.
-/
structure TruthTableLocalPRG (n : Nat) where
  seedBits : Nat
  gen : BitVec seedBits → TruthTable n
  imageSizeBound : Nat
  image_easy : ∀ seed : BitVec seedBits,
    treeMCSPPredicate n imageSizeBound (gen seed)

/--
Acceptance probability of a truth-table algorithm under the PRG image
distribution induced by uniform seeds.
-/
noncomputable def seedAcceptanceProbability
    {n : Nat}
    (prg : TruthTableLocalPRG n)
    (A : TruthTable n → Bool) : Rat :=
  bitVecAcceptanceProbability (fun seed => A (prg.gen seed))

/-- Extensionality for the uniform bit-vector acceptance probability. -/
theorem bitVecAcceptanceProbability_congr
    {m : Nat}
    {A B : BitVec m → Bool}
    (hAB : A = B) :
    bitVecAcceptanceProbability A = bitVecAcceptanceProbability B := by
  cases hAB
  rfl

/-- Extensionality for the PRG-image acceptance probability. -/
theorem seedAcceptanceProbability_congr
    {n : Nat}
    (prg : TruthTableLocalPRG n)
    {A B : TruthTable n → Bool}
    (hAB : A = B) :
    seedAcceptanceProbability prg A = seedAcceptanceProbability prg B := by
  exact bitVecAcceptanceProbability_congr (m := prg.seedBits) (by
    cases hAB
    rfl)

/-- Extensionality for the uniform truth-table acceptance probability. -/
theorem uniformTruthTableAcceptanceProbability_congr
    {n : Nat}
    {A B : TruthTable n → Bool}
    (hAB : A = B) :
    uniformTruthTableAcceptanceProbability A =
      uniformTruthTableAcceptanceProbability B := by
  exact bitVecAcceptanceProbability_congr hAB

/--
If every `m`-bit input is accepted, the corresponding uniform acceptance
probability is exactly `1`.
-/
theorem bitVecAcceptanceProbability_eq_one_of_forall_accept
    {m : Nat}
    {A : BitVec m → Bool}
    (hAccept : ∀ x : BitVec m, A x = true) :
    bitVecAcceptanceProbability A = 1 := by
  classical
  have hFilter :
      (Finset.univ : Finset (BitVec m)).filter (fun x => A x = true) =
        (Finset.univ : Finset (BitVec m)) := by
    ext x
    simp [hAccept x]
  have hPowNeZero : (2 ^ m : Rat) ≠ 0 := by positivity
  calc
    bitVecAcceptanceProbability A
        = (((Finset.univ : Finset (BitVec m)).card : Rat) / (2 ^ m : Rat)) := by
            simp [bitVecAcceptanceProbability, hFilter]
    _ = ((2 ^ m : Rat) / (2 ^ m : Rat)) := by
          simp
    _ = 1 := by
          simp [hPowNeZero]

/--
If every PRG output is accepted, the acceptance probability under the uniform
seed distribution is exactly `1`.
-/
theorem seedAcceptanceProbability_eq_one_of_forall_accept
    {n : Nat}
    (prg : TruthTableLocalPRG n)
    {A : TruthTable n → Bool}
    (hAccept : ∀ seed : BitVec prg.seedBits, A (prg.gen seed) = true) :
    seedAcceptanceProbability prg A = 1 := by
  exact bitVecAcceptanceProbability_eq_one_of_forall_accept hAccept

/--
Full pseudorandomness surface against a size-bounded non-uniform class:
uniform truth tables and the PRG image are indistinguishable up to error
`epsilon`.
-/
noncomputable def FoolsBoundedTruthTableClass
    {n : Nat}
    (prg : TruthTableLocalPRG n)
    (C : CircuitFamilyClass)
    (maxSize : Nat)
    (epsilon : Rat) : Prop :=
  ∀ c : C.Family (Pnp3.Models.Partial.tableLen n),
    C.size c ≤ maxSize →
      |uniformTruthTableAcceptanceProbability (fun tt => C.eval c tt) -
          seedAcceptanceProbability prg (fun tt => C.eval c tt)| ≤ epsilon

/--
One-sided variant of the same fooling property.  This is the exact inequality
consumed by the lower-bound transfer theorem.
-/
noncomputable def OneSidedFoolsBoundedTruthTableClass
    {n : Nat}
    (prg : TruthTableLocalPRG n)
    (C : CircuitFamilyClass)
    (maxSize : Nat)
    (epsilon : Rat) : Prop :=
  ∀ c : C.Family (Pnp3.Models.Partial.tableLen n),
    C.size c ≤ maxSize →
      seedAcceptanceProbability prg (fun tt => C.eval c tt) ≤
        uniformTruthTableAcceptanceProbability (fun tt => C.eval c tt) + epsilon

/--
Two-sided pseudorandomness implies the one-sided lower-transfer inequality.
-/
theorem oneSidedFoolsBoundedTruthTableClass_of_foolsBounded
    {n : Nat}
    {prg : TruthTableLocalPRG n}
    {C : CircuitFamilyClass}
    {maxSize : Nat}
    {epsilon : Rat}
    (hFool : FoolsBoundedTruthTableClass prg C maxSize epsilon) :
    OneSidedFoolsBoundedTruthTableClass prg C maxSize epsilon := by
  intro c hcSize
  have hAbs := hFool c hcSize
  have hLeft : -epsilon ≤
      uniformTruthTableAcceptanceProbability (fun tt => C.eval c tt) -
        seedAcceptanceProbability prg (fun tt => C.eval c tt) :=
    (abs_le.mp hAbs).1
  linarith

end AlgorithmsToLowerBounds
end Pnp4
