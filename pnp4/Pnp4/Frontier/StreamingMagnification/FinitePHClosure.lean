import Pnp4.Frontier.StreamingMagnification.OperationalUniformity
import Pnp4.Frontier.StreamingMagnification.FixedBitstringCodec

/-!
# Finite quantifier closure for the operational uniform model

This module isolates the elementary finite-projection part of a polynomial
hierarchy collapse argument for `OperationalUniformity`.  An existential
projection ranges over the canonical witness length `n ^ k + k` and reuses a
single operational decider for the matrix language as its verifier.  A
universal projection is defined by Boolean complement.

Closing either projection back into `UniformP` is stated only under the
explicit hypothesis `forall L, UniformNP L -> UniformP L`.  In particular,
this file supplies no parser, no operational machine for a Stream-Merge row,
and no runtime bridge from a bounded finite Boolean definition to
`OperationalTM`.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace FinitePHClosure

open Pnp3.ComplexityInterfaces
open OperationalUniformity
open FixedBitstringCodec

/-! ## Finite existential projection -/

/--
Existentially project a canonical polynomial-length suffix from a language.
The matrix is evaluated at the actual concatenated input length.
-/
def ExistsProject (witnessExponent : Nat) (relation : Language) : Language :=
  fun inputLength input =>
    decide (exists index : Fin
        (2 ^ certificateLength inputLength witnessExponent),
      relation
          (inputLength + certificateLength inputLength witnessExponent)
          (concatBitstring input (unrank index)) = true)

@[simp] theorem existsProject_eq_true_iff
    (witnessExponent : Nat) (relation : Language)
    (inputLength : Nat) (input : Bitstring inputLength) :
    ExistsProject witnessExponent relation inputLength input = true <->
      exists witness : Bitstring
          (certificateLength inputLength witnessExponent),
        relation
            (inputLength + certificateLength inputLength witnessExponent)
            (concatBitstring input witness) = true := by
  unfold ExistsProject
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨index, hindex⟩
    exact ⟨unrank index, hindex⟩
  · rintro ⟨witness, hwitness⟩
    refine ⟨rank witness, ?_⟩
    rw [unrank_rank]
    exact hwitness

/-- A `UniformP` matrix gives a `UniformNP` existential projection. -/
theorem uniformP_existsProject
    {witnessExponent : Nat} {relation : Language}
    (hrelation : UniformP relation) :
    UniformNP (ExistsProject witnessExponent relation) := by
  rcases hrelation with ⟨program, hprogram⟩
  refine ⟨program, witnessExponent, ?_⟩
  intro inputLength input
  rw [existsProject_eq_true_iff]
  constructor
  · rintro ⟨witness, hwitness⟩
    exact ⟨witness, by simpa [hprogram] using hwitness⟩
  · rintro ⟨witness, hwitness⟩
    exact ⟨witness, by simpa [hprogram] using hwitness⟩

/-! ## Finite universal projection -/

/-- Universal projection, implemented as `not exists not`. -/
def ForallProject (witnessExponent : Nat) (relation : Language) : Language :=
  complementLanguage
    (ExistsProject witnessExponent (complementLanguage relation))

@[simp] theorem forallProject_eq_true_iff
    (witnessExponent : Nat) (relation : Language)
    (inputLength : Nat) (input : Bitstring inputLength) :
    ForallProject witnessExponent relation inputLength input = true <->
      forall witness : Bitstring
          (certificateLength inputLength witnessExponent),
        relation
            (inputLength + certificateLength inputLength witnessExponent)
            (concatBitstring input witness) = true := by
  change
    Bool.not
        (ExistsProject witnessExponent (complementLanguage relation)
          inputLength input) = true <-> _
  constructor
  · intro hnot witness
    cases hrelation : relation
        (inputLength + certificateLength inputLength witnessExponent)
        (concatBitstring input witness) with
    | false =>
        exfalso
        have hexists :
            ExistsProject witnessExponent (complementLanguage relation)
                inputLength input = true :=
          (existsProject_eq_true_iff witnessExponent
            (complementLanguage relation) inputLength input).2
            ⟨witness, by simp [complementLanguage, hrelation]⟩
        simp [hexists] at hnot
    | true => rfl
  · intro hall
    cases hproject :
        ExistsProject witnessExponent (complementLanguage relation)
          inputLength input with
    | false => rfl
    | true =>
        exfalso
        rcases
            (existsProject_eq_true_iff witnessExponent
              (complementLanguage relation) inputLength input).1 hproject with
          ⟨witness, hwitness⟩
        simp [complementLanguage, hall witness] at hwitness

/-! ## Closure under an explicit NP-to-P collapse hypothesis -/

/-- The exact collapse hypothesis used below; no collapse is proved here. -/
abbrev UniformNPCollapse : Prop :=
  forall language : Language, UniformNP language -> UniformP language

/-- Equality of the two repaired class predicates implies the local collapse
used in this file.  This is not a bridge to conventional `P = NP`. -/
theorem uniformNPCollapse_of_class_eq
    (hclasses : UniformP = UniformNP) :
    UniformNPCollapse := by
  intro language hlanguage
  rw [hclasses]
  exact hlanguage

theorem uniformP_existsProject_of_collapse
    (collapse : UniformNPCollapse)
    {witnessExponent : Nat} {relation : Language}
    (hrelation : UniformP relation) :
    UniformP (ExistsProject witnessExponent relation) :=
  collapse _ (uniformP_existsProject hrelation)

theorem uniformP_forallProject_of_collapse
    (collapse : UniformNPCollapse)
    {witnessExponent : Nat} {relation : Language}
    (hrelation : UniformP relation) :
    UniformP (ForallProject witnessExponent relation) := by
  apply uniformP_complement
  apply collapse
  exact uniformP_existsProject (uniformP_complement hrelation)

/-! ## Generic existential-universal-existential closure -/

/--
The nested projection corresponding to an existential-universal-existential
prefix.  Each suffix length is computed from the input length visible at that
projection; this definition does not claim an encoding of any external
fixed-slice request language.
-/
def EAEProject (outerExponent middleExponent innerExponent : Nat)
    (relation : Language) : Language :=
  ExistsProject outerExponent
    (ForallProject middleExponent
      (ExistsProject innerExponent relation))

/--
Under the explicit `UniformNP`-to-`UniformP` collapse, a `UniformP` matrix
remains in `UniformP` after an E-A-E prefix.  The proof applies the three
closure steps from the innermost quantifier outward.
-/
theorem uniformP_eaeProject_of_collapse
    (collapse : UniformNPCollapse)
    {outerExponent middleExponent innerExponent : Nat}
    {relation : Language}
    (hrelation : UniformP relation) :
    UniformP
      (EAEProject outerExponent middleExponent innerExponent relation) := by
  unfold EAEProject
  apply uniformP_existsProject_of_collapse collapse
  apply uniformP_forallProject_of_collapse collapse
  exact uniformP_existsProject_of_collapse collapse hrelation

/-- The same repaired-model E-A-E closure, specialized to equality of the
repaired deterministic and nondeterministic class predicates. -/
theorem uniformP_eaeProject_of_class_eq
    (hclasses : UniformP = UniformNP)
    {outerExponent middleExponent innerExponent : Nat}
    {relation : Language}
    (hrelation : UniformP relation) :
    UniformP
      (EAEProject outerExponent middleExponent innerExponent relation) :=
  uniformP_eaeProject_of_collapse
    (uniformNPCollapse_of_class_eq hclasses) hrelation

end FinitePHClosure
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.FinitePHClosure.existsProject_eq_true_iff
#print axioms Pnp4.Frontier.StreamingMagnification.FinitePHClosure.uniformP_existsProject
#print axioms Pnp4.Frontier.StreamingMagnification.FinitePHClosure.forallProject_eq_true_iff
#print axioms Pnp4.Frontier.StreamingMagnification.FinitePHClosure.uniformNPCollapse_of_class_eq
#print axioms Pnp4.Frontier.StreamingMagnification.FinitePHClosure.uniformP_eaeProject_of_collapse
#print axioms Pnp4.Frontier.StreamingMagnification.FinitePHClosure.uniformP_eaeProject_of_class_eq
