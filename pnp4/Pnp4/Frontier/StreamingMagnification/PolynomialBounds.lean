import Pnp4.Frontier.StreamingMagnification.StreamingRAM

/-!
# Exact polynomial streaming quantifiers

This module records the quantifier order needed by the MMW lower-bound
antecedent.  There is one uniform `Program`, followed by existential resource
exponents, constants, and an eventual cutoff.  Correctness and termination
hold at every length and on every input.  Only resource bounds are eventual.

The correctness argument is deliberately an explicit predicate on completed
operational runs.  It can later be instantiated with tagged total search-MCSP
semantics, but it is not a field containing a solver, lower bound, contract,
source, provider, or typeclass assumption.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace PolynomialBounds

open StreamingRAM

/-- The physical truth-table length corresponding to `n` Boolean variables. -/
def truthTableLength (n : Nat) : Nat := 2 ^ n

/-- The requested MMW threshold schedule.  A capstone using it should retain
the separate hypothesis `1 <= k`; the definition remains total at every `k`. -/
def thresholdSchedule (k n : Nat) : Nat := max n (n ^ k)

/-- An explicit coefficient-and-exponent polynomial envelope.  The additive
copy of the coefficient handles small values without an asymptotic notation. -/
def polynomialEnvelope (constant exponent value : Nat) : Nat :=
  constant * (value + 1) ^ exponent + constant

/-- A semantic specification for completed runs on inputs whose physical
length is `inputLength n`.  Keeping the program as an explicit argument makes
uniformity visible in the quantifier normal form. -/
abbrev CompletedRunSpecification (inputLength : Nat -> Nat) :=
  (program : Program) ->
  (n : Nat) ->
  (input : Input (inputLength n)) ->
  CompletedRun program input -> Prop

/-- Correctness and successful explicit completion at every length, including
the finitely many lengths below an eventual resource cutoff. -/
def CorrectAtAllLengths
    (inputLength : Nat -> Nat)
    (correct : CompletedRunSpecification inputLength)
    (program : Program) : Prop :=
  forall n (input : Input (inputLength n)),
    exists completed : CompletedRun program input,
      correct program n input completed

/-- Eventual resource bounds for every table and every completion witness.
Runs are deterministic and terminal configurations stutter without changing
their counters, so quantifying over all completion witnesses cannot select a
cheaper late witness. -/
def EventuallyPolynomialResources
    (inputLength threshold : Nat -> Nat)
    (program : Program)
    (spaceExponent updateExponent : Nat)
    (spaceConstant updateConstant reportConstant cutoff : Nat) : Prop :=
  forall n, cutoff <= n ->
    forall (input : Input (inputLength n))
      (completed : CompletedRun program input),
      completed.spaceUsed <=
          polynomialEnvelope spaceConstant spaceExponent (threshold n) /\
        completed.maxUpdateGap <=
          polynomialEnvelope updateConstant updateExponent (threshold n) /\
        completed.reportTime <=
          polynomialEnvelope reportConstant updateExponent (threshold n)

/-- Exact positive predicate: one uniform program, then existential polynomial
parameters, then all-length correctness plus eventual worst-case resources. -/
def PolyStreamingSolvable
    (inputLength threshold : Nat -> Nat)
    (correct : CompletedRunSpecification inputLength) : Prop :=
  exists program : Program,
  exists spaceExponent updateExponent : Nat,
  exists spaceConstant updateConstant reportConstant cutoff : Nat,
    CorrectAtAllLengths inputLength correct program /\
      EventuallyPolynomialResources inputLength threshold program
        spaceExponent updateExponent
        spaceConstant updateConstant reportConstant cutoff

/-- The requested streaming lower bound negates the complete existence
statement, including the program and every possible exponent and constant. -/
def NoPolyStreamingSolver
    (inputLength threshold : Nat -> Nat)
    (correct : CompletedRunSpecification inputLength) : Prop :=
  Not (PolyStreamingSolvable inputLength threshold correct)

/-- The positive predicate exposed without helper definitions, for quantifier
audits and downstream surface tests. -/
theorem polyStreamingSolvable_iff
    (inputLength threshold : Nat -> Nat)
    (correct : CompletedRunSpecification inputLength) :
    PolyStreamingSolvable inputLength threshold correct <->
      exists program : Program,
      exists spaceExponent updateExponent : Nat,
      exists spaceConstant updateConstant reportConstant cutoff : Nat,
        (forall n (input : Input (inputLength n)),
          exists completed : CompletedRun program input,
            correct program n input completed) /\
        (forall n, cutoff <= n ->
          forall (input : Input (inputLength n))
            (completed : CompletedRun program input),
            completed.spaceUsed <=
                polynomialEnvelope spaceConstant spaceExponent (threshold n) /\
              completed.maxUpdateGap <=
                polynomialEnvelope updateConstant updateExponent (threshold n) /\
              completed.reportTime <=
                polynomialEnvelope reportConstant updateExponent (threshold n)) :=
  Iff.rfl

/-- The lower-bound predicate exposed as the negation of the entire normal
form.  In particular it is not a claim about one fixed machine or exponent. -/
theorem noPolyStreamingSolver_iff
    (inputLength threshold : Nat -> Nat)
    (correct : CompletedRunSpecification inputLength) :
    NoPolyStreamingSolver inputLength threshold correct <->
      Not (
        exists program : Program,
        exists spaceExponent updateExponent : Nat,
        exists spaceConstant updateConstant reportConstant cutoff : Nat,
          (forall n (input : Input (inputLength n)),
            exists completed : CompletedRun program input,
              correct program n input completed) /\
          (forall n, cutoff <= n ->
            forall (input : Input (inputLength n))
              (completed : CompletedRun program input),
              completed.spaceUsed <=
                  polynomialEnvelope spaceConstant spaceExponent (threshold n) /\
                completed.maxUpdateGap <=
                  polynomialEnvelope updateConstant updateExponent (threshold n) /\
                completed.reportTime <=
                  polynomialEnvelope reportConstant updateExponent
                    (threshold n))) :=
  Iff.rfl

/-- Specialization of the generic predicate to truth tables and `s_k`. -/
def MMWPolyStreamingSolvable
    (k : Nat)
    (correct : CompletedRunSpecification truthTableLength) : Prop :=
  PolyStreamingSolvable truthTableLength (thresholdSchedule k) correct

/-- Full lower-bound specialization for truth tables and `s_k`. -/
def NoMMWPolyStreamingSolver
    (k : Nat)
    (correct : CompletedRunSpecification truthTableLength) : Prop :=
  NoPolyStreamingSolver truthTableLength (thresholdSchedule k) correct

end PolynomialBounds
end StreamingMagnification
end Frontier
end Pnp4
